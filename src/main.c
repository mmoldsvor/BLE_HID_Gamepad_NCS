#include <zephyr/types.h>
#include <stddef.h>
#include <string.h>
#include <errno.h>
#include <sys/printk.h>
#include <sys/byteorder.h>
#include <zephyr.h>
#include <device.h>
#include <drivers/gpio.h>
#include <soc.h>
#include <assert.h>
#include <spinlock.h>

#include <settings/settings.h>

#include <bluetooth/bluetooth.h>
#include <bluetooth/hci.h>
#include <bluetooth/conn.h>
#include <bluetooth/uuid.h>
#include <bluetooth/gatt.h>

#include <bluetooth/services/hids.h>
#include <bluetooth/services/dis.h>

#include <hal/nrf_saadc.h>
#include <drivers/adc.h>

#define DEVICE_NAME CONFIG_BT_DEVICE_NAME
#define DEVICE_NAME_LEN (sizeof(DEVICE_NAME) - 1)

#define BASE_USB_HID_SPEC_VERSION 0x0101

#define ADV_LED_BLINK_INTERVAL 1000

#define ADV_STATUS_LED 11
#define CON_STATUS_LED 12

#define BUTTON_X_MASK BIT(6)
#define BUTTON_Y_MASK BIT(5)
#define BUTTON_A_MASK BIT(7)
#define BUTTON_B_MASK BIT(4)

#define BUTTON_DOWN_MASK BIT(19)
#define BUTTON_RIGHT_MASK BIT(18)
#define BUTTON_LEFT_MASK BIT(20)
#define BUTTON_UP_MASK BIT(21)

#define BUTTON_HOME_MASK BIT(13)
#define BUTTON_MINUS_MASK BIT(14)
#define BUTTON_PLUS_MASK BIT(10)

#define BUTTON_LEFT_TRIGGER_BUTTON_MASK BIT(24)
#define BUTTON_LEFT_BUMPER_MASK BIT(23)
#define BUTTON_RIGHT_TRIGGER_BUTTON_MASK BIT(26)
#define BUTTON_RIGHT_BUMPER_MASK BIT(25)

#define BUTTON_LEFT_STICK_BUTTON_MASK BIT(15)
#define BUTTON_RIGHT_STICK_BUTTON_MASK BIT(16)

#define KEY_ADV_MASK BIT(13)

/* Key used to accept or reject passkey value */
#define KEY_PAIRING_ACCEPT BIT(10)
#define KEY_PAIRING_REJECT BIT(14)

/* HIDs queue elements. */
#define HIDS_QUEUE_SIZE 10

#define INPUT_REP_GAMEPAD_REF_ID 1

#define INPUT_REPORT_GAMEPAD_BUTTONS_MAX_LEN 2
#define INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN 2
#define INPUT_REPORT_GAMEPAD_MAX_LEN INPUT_REPORT_GAMEPAD_BUTTONS_MAX_LEN + INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN + INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN

#define HIDS_STACK_SIZE 2048
#define HIDS_PRIORITY 5

#define SAADC_STACK_SIZE 2048
#define SAADC_PRIORITY 10

#define ADC_DEVICE_NAME DT_LABEL(DT_INST(0, nordic_nrf_saadc))
#define ADC_RESOLUTION 8
#define ADC_GAIN ADC_GAIN_1_4
#define ADC_REFERENCE ADC_REF_VDD_1_4
#define ADC_ACQUISITION_TIME ADC_ACQ_TIME(ADC_ACQ_TIME_MICROSECONDS, 10)

#define SAADC_INTERVAL_MSEC 15
#define BUFFER_SIZE 8

// Position in internal report table
enum
{
    INPUT_REP_GAMEPAD_IDX = 0
};

/* HIDS instance. */
BT_HIDS_DEF(hids_obj,
            INPUT_REPORT_GAMEPAD_BUTTONS_MAX_LEN,
            INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN,
            INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN);

static volatile bool is_adv;

static const struct bt_data ad[] = {
    BT_DATA_BYTES(BT_DATA_GAP_APPEARANCE,
                  (CONFIG_BT_DEVICE_APPEARANCE >> 0) & 0xff,
                  (CONFIG_BT_DEVICE_APPEARANCE >> 8) & 0xff),
    BT_DATA_BYTES(BT_DATA_FLAGS, (BT_LE_AD_GENERAL | BT_LE_AD_NO_BREDR)),
    BT_DATA_BYTES(BT_DATA_UUID16_ALL,
                  0x12, 0x18), /* HID Service */

};

static const struct bt_data sd[] = {
    BT_DATA(BT_DATA_NAME_COMPLETE, DEVICE_NAME, DEVICE_NAME_LEN),
};

static struct conn_mode
{
    struct bt_conn *conn;
} conn_mode[CONFIG_BT_HIDS_MAX_CLIENT_COUNT];

typedef struct
{
    uint8_t horizontal;
    uint8_t vertical;
} thumbstick_state;

typedef struct
{
    thumbstick_state left;
    thumbstick_state right;
} thumbstick_collection;

typedef struct
{
    uint8_t first;
    uint8_t second;
} button_collection;

typedef struct
{
    button_collection buttons;
    thumbstick_collection thumbsticks;
} gamepad_event_state;

static struct k_work pairing_work;
struct pairing_data_mitm
{
    struct bt_conn *conn;
    unsigned int passkey;
};

static struct k_work num_comp_reply_work;
static bool num_comp_reply_value;

const struct device *adc_dev;
struct k_timer saadc_timer;
static struct k_work saadc_work;

static nrf_saadc_input_t saadc_inputs[4] = {
    NRF_SAADC_INPUT_AIN1,  // Left thumbstick vertical
    NRF_SAADC_INPUT_AIN0,  // Left thumbstick horizontal
    NRF_SAADC_INPUT_AIN6,  // Right thumbstick vertical
    NRF_SAADC_INPUT_AIN7}; // Right thumbstick horizontal

K_MSGQ_DEFINE(mitm_queue,
              sizeof(struct pairing_data_mitm),
              CONFIG_BT_HIDS_MAX_CLIENT_COUNT,
              4);

static volatile bool data_to_send;
static struct k_work hids_work;

K_MSGQ_DEFINE(hids_queue,
              sizeof(gamepad_event_state),
              HIDS_QUEUE_SIZE,
              4);

K_THREAD_STACK_DEFINE(hids_stack, HIDS_STACK_SIZE);
struct k_work_q hids_work_q;

K_THREAD_STACK_DEFINE(saadc_stack, SAADC_STACK_SIZE);
struct k_work_q saadc_work_q;

static int16_t saadc_buffer[BUFFER_SIZE];

static struct gamepad_state
{
    uint32_t buttons;
    thumbstick_state thumbsticks[2];
} hid_gamepad_state;

static struct gpio_callback button_cb_data;

static const struct gpio_dt_spec button[] = {
    GPIO_DT_SPEC_GET(DT_ALIAS(sw0), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw1), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw2), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw3), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw4), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw5), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw6), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw7), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw8), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw9), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw10), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw11), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw12), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw13), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw14), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(sw15), gpios),
};

static const struct gpio_dt_spec led[] = {
    GPIO_DT_SPEC_GET(DT_ALIAS(led0), gpios),
    GPIO_DT_SPEC_GET(DT_ALIAS(led1), gpios),
};

static void advertising_start(void)
{
    int err;
    struct bt_le_adv_param *adv_param = BT_LE_ADV_PARAM(
        BT_LE_ADV_OPT_CONNECTABLE |
            BT_LE_ADV_OPT_ONE_TIME,
        BT_GAP_ADV_FAST_INT_MIN_2,
        BT_GAP_ADV_FAST_INT_MAX_2,
        NULL);

    err = bt_le_adv_start(adv_param, ad, ARRAY_SIZE(ad), sd,
                          ARRAY_SIZE(sd));
    if (err)
    {
        if (err == -EALREADY)
        {
            printk("Advertising continued\n");
        }
        else
        {
            printk("Advertising failed to start (err %d)\n", err);
        }

        return;
    }

    is_adv = true;
    printk("Advertising successfully started\n");
}

static void pairing_process(struct k_work *work)
{
    int err;
    struct pairing_data_mitm pairing_data;

    char addr[BT_ADDR_LE_STR_LEN];

    err = k_msgq_peek(&mitm_queue, &pairing_data);
    if (err)
    {
        return;
    }

    bt_addr_le_to_str(bt_conn_get_dst(pairing_data.conn),
                      addr, sizeof(addr));

    printk("Passkey for %s: %06u\n", addr, pairing_data.passkey);
    printk("Press Button 1 to confirm, Button 2 to reject.\n");
}

static void connected(struct bt_conn *conn, uint8_t err)
{
    char addr[BT_ADDR_LE_STR_LEN];

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    if (err)
    {
        printk("Failed to connect to %s (%u)\n", addr, err);
        return;
    }

    printk("Connected %s\n", addr);
    gpio_pin_set_raw(led[0].port, CON_STATUS_LED, 1);

    err = bt_hids_connected(&hids_obj, conn);

    if (err)
    {
        printk("Failed to notify HID service about connection\n");
        return;
    }

    for (size_t i = 0; i < CONFIG_BT_HIDS_MAX_CLIENT_COUNT; i++)
    {
        if (!conn_mode[i].conn)
        {
            conn_mode[i].conn = conn;
            break;
        }
    }

    is_adv = false;
}

static void disconnected(struct bt_conn *conn, uint8_t reason)
{
    int err;
    bool is_any_dev_connected = false;
    char addr[BT_ADDR_LE_STR_LEN];

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    printk("Disconnected from %s (reason %u)\n", addr, reason);

    err = bt_hids_disconnected(&hids_obj, conn);

    if (err)
    {
        printk("Failed to notify HID service about disconnection\n");
    }

    for (size_t i = 0; i < CONFIG_BT_HIDS_MAX_CLIENT_COUNT; i++)
    {
        if (conn_mode[i].conn == conn)
        {
            conn_mode[i].conn = NULL;
        }
        else
        {
            if (conn_mode[i].conn)
            {
                is_any_dev_connected = true;
            }
        }
    }

    if (!is_any_dev_connected)
    {
        gpio_pin_set_raw(led[0].port, CON_STATUS_LED, 0);
    }

    advertising_start();
}

static void security_changed(struct bt_conn *conn, bt_security_t level,
                             enum bt_security_err err)
{
    char addr[BT_ADDR_LE_STR_LEN];

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    if (!err)
    {
        printk("Security changed: %s level %u\n", addr, level);
    }
    else
    {
        printk("Security failed: %s level %u err %d\n", addr, level,
               err);
    }
}

static void le_param_updated(struct bt_conn *conn, uint16_t interval, 
                              uint16_t latency, uint16_t timeout)
{
    printk("INTERVAL: %d\n", interval);
}

static struct bt_conn_cb conn_callbacks = {
    .connected = connected,
    .disconnected = disconnected,
    .security_changed = security_changed,
    .le_param_updated = le_param_updated,
};

static void hid_init(void)
{
    int err;
    struct bt_hids_init_param hids_init_obj = {0};
    struct bt_hids_inp_rep *hids_inp_rep;

    static const uint8_t report_map[] = {
        0x05, 0x01,       // USAGE_PAGE (Generic Desktop)
        0x09, 0x05,       // USAGE (Game Pad)
        0xa1, 0x01,       // COLLECTION (Application)
        0x85, 0x01,       //   REPORT_ID (1)
        0x09, 0x01,       //   USAGE (Pointer)
        0xa1, 0x00,       //   COLLECTION (Physical)
        0x05, 0x09,       //     USAGE_PAGE (Button)
        0x95, 0x10,       //     REPORT_COUNT (16)
        0x75, 0x01,       //     REPORT_SIZE (1)
        0x19, 0x01,       //     USAGE_MINIMUM (Button 1)
        0x29, 0x10,       //     USAGE_MAXIMUM (Button 16)
        0x15, 0x00,       //     LOGICAL_MINIMUM (0)
        0x25, 0x01,       //     LOGICAL_MAXIMUM (1)
        0x81, 0x02,       //     INPUT (Data,Var,Abs)
        0xc0,             //   END_COLLECTION
        0x05, 0x01,       //   USAGE_PAGE (Generic Desktop)
        0x09, 0x01,       //   USAGE (Pointer)
        0xa1, 0x00,       //   COLLECTION (Physical)
        0x75, 0x08,       //     REPORT_SIZE (8)
        0x95, 0x02,       //     REPORT_COUNT (2)
        0x09, 0x30,       //     USAGE (X)
        0x09, 0x31,       //     USAGE (Y)
        0x15, 0x00,       //     LOGICAL_MINIMUM (0)
        0x26, 0xff, 0x00, //     LOGICAL_MAXIMUM (255)
        0x81, 0x02,       //     INPUT (Data,Var,Abs)
        0xc0,             //   END_COLLECTION
        0x09, 0x01,       //   USAGE (Pointer)
        0xa1, 0x00,       //   COLLECTION (Physical)
        0x75, 0x08,       //     REPORT_SIZE (8)
        0x95, 0x02,       //     REPORT_COUNT (2)
        0x09, 0x32,       //     USAGE (Z)
        0x09, 0x33,       //     USAGE (Rx)
        0x15, 0x00,       //     LOGICAL_MINIMUM (0)
        0x26, 0xff, 0x00, //     LOGICAL_MAXIMUM (255)
        0x81, 0x02,       //     INPUT (Data,Var,Abs)
        0xc0,             //   END_COLLECTION
        0xc0              // END_COLLECTION
    };

    hids_init_obj.rep_map.data = report_map;
    hids_init_obj.rep_map.size = sizeof(report_map);

    hids_init_obj.info.bcd_hid = BASE_USB_HID_SPEC_VERSION;
    hids_init_obj.info.b_country_code = 0x00;
    hids_init_obj.info.flags = (BT_HIDS_REMOTE_WAKE | BT_HIDS_NORMALLY_CONNECTABLE);

    hids_inp_rep = &hids_init_obj.inp_rep_group_init.reports[INPUT_REP_GAMEPAD_IDX];
    hids_inp_rep->size = INPUT_REPORT_GAMEPAD_MAX_LEN;
    hids_inp_rep->id = INPUT_REP_GAMEPAD_REF_ID;
    hids_init_obj.inp_rep_group_init.cnt++;

    err = bt_hids_init(&hids_obj, &hids_init_obj);
    __ASSERT(err == 0, "HIDS initialization failed\n");
}

static void auth_passkey_display(struct bt_conn *conn, unsigned int passkey)
{
    char addr[BT_ADDR_LE_STR_LEN];

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    printk("Passkey for %s: %06u\n", addr, passkey);
}

static void auth_passkey_confirm(struct bt_conn *conn, unsigned int passkey)
{
    int err;

    struct pairing_data_mitm pairing_data;

    pairing_data.conn = bt_conn_ref(conn);
    pairing_data.passkey = passkey;

    err = k_msgq_put(&mitm_queue, &pairing_data, K_NO_WAIT);
    if (err)
    {
        printk("Pairing queue is full. Purge previous data.\n");
    }

    /* In the case of multiple pairing requests, trigger
	 * pairing confirmation which needed user interaction only
	 * once to avoid display information about all devices at
	 * the same time. Passkey confirmation for next devices will
	 * be proccess from queue after handling the earlier ones.
	 */
    if (k_msgq_num_used_get(&mitm_queue) == 1)
    {
        k_work_submit(&pairing_work);
    }
}

static void auth_cancel(struct bt_conn *conn)
{
    char addr[BT_ADDR_LE_STR_LEN];

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    printk("Pairing cancelled: %s\n", addr);
}

static void pairing_confirm(struct bt_conn *conn)
{
    char addr[BT_ADDR_LE_STR_LEN];

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    bt_conn_auth_pairing_confirm(conn);

    printk("Pairing confirmed: %s\n", addr);
}

static void pairing_complete(struct bt_conn *conn, bool bonded)
{
    char addr[BT_ADDR_LE_STR_LEN];

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    printk("Pairing completed: %s, bonded: %d\n", addr, bonded);
}

static void pairing_failed(struct bt_conn *conn, enum bt_security_err reason)
{
    char addr[BT_ADDR_LE_STR_LEN];
    struct pairing_data_mitm pairing_data;

    if (k_msgq_peek(&mitm_queue, &pairing_data) != 0)
    {
        return;
    }

    if (pairing_data.conn == conn)
    {
        bt_conn_unref(pairing_data.conn);
        k_msgq_get(&mitm_queue, &pairing_data, K_NO_WAIT);
    }

    bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

    printk("Pairing failed conn: %s, reason %d\n", addr, reason);
}

static struct bt_conn_auth_cb conn_auth_callbacks = {
    .passkey_display = auth_passkey_display,
    .passkey_confirm = auth_passkey_confirm,
    .cancel = auth_cancel,
    .pairing_confirm = pairing_confirm,
    .pairing_complete = pairing_complete,
    .pairing_failed = pairing_failed};

static void num_comp_reply(bool accept)
{
    struct pairing_data_mitm pairing_data;
    struct bt_conn *conn;

    if (k_msgq_get(&mitm_queue, &pairing_data, K_NO_WAIT) != 0)
    {
        return;
    }

    conn = pairing_data.conn;

    if (accept)
    {
        bt_conn_auth_passkey_confirm(conn);
        printk("Numeric Match, conn %p\n", conn);
    }
    else
    {
        bt_conn_auth_cancel(conn);
        printk("Numeric Reject, conn %p\n", conn);
    }

    bt_conn_unref(pairing_data.conn);

    if (k_msgq_num_used_get(&mitm_queue))
    {
        k_work_submit(&pairing_work);
    }
}

static void num_comp_reply_handler(struct k_work *work)
{
    int err;

    num_comp_reply(num_comp_reply_value);
}

static int gamepad_report_send(struct bt_conn *conn, gamepad_event_state state)
{
    int err = 0;
    uint8_t data[INPUT_REPORT_GAMEPAD_MAX_LEN];

    data[0] = state.buttons.first;
    data[1] = state.buttons.second;
    data[2] = state.thumbsticks.left.vertical;
    data[3] = state.thumbsticks.left.horizontal;
    data[4] = state.thumbsticks.right.vertical;
    data[5] = state.thumbsticks.right.horizontal;

    err = bt_hids_inp_rep_send(&hids_obj, conn, INPUT_REP_GAMEPAD_IDX, data, sizeof(data), NULL);

    return err;
}

static int report_send(gamepad_event_state state)
{
    for (size_t i = 0; i < CONFIG_BT_HIDS_MAX_CLIENT_COUNT; i++)
    {
        if (conn_mode[i].conn && bt_conn_get_security(conn_mode[i].conn) == BT_SECURITY_L4)
        {
            int err;
            err = gamepad_report_send(conn_mode[i].conn, state);

            if (err)
            {
                printk("Gamepad report send error: %d\n", err);
                return err;
            }
        }
    }
    return 0;
}

static void gamepad_button_changed(uint8_t button, bool down)
{
    hid_gamepad_state.buttons = (hid_gamepad_state.buttons & ~(1 << button)) | (down << button);
    data_to_send = true;
}

static void gamepad_thumbstick_changed(uint8_t thumbstick, uint8_t vertical, uint8_t horizontal)
{
    hid_gamepad_state.thumbsticks[thumbstick].vertical = 255 - vertical;
    hid_gamepad_state.thumbsticks[thumbstick].horizontal = horizontal;
    data_to_send = true;
}

static void gamepad_event_handler(struct k_work *work)
{
    gamepad_event_state state;

    while (!k_msgq_get(&hids_queue, &state, K_NO_WAIT))
    {
        report_send(state);
    }
}

static int add_to_queue(void)
{
    int err;

    gamepad_event_state state;

    state.buttons.first = (uint8_t)hid_gamepad_state.buttons;
    state.buttons.second = (uint8_t)(hid_gamepad_state.buttons >> 8);

    state.thumbsticks.left.vertical = hid_gamepad_state.thumbsticks[0].vertical;
    state.thumbsticks.left.horizontal = hid_gamepad_state.thumbsticks[0].horizontal;

    state.thumbsticks.right.vertical = hid_gamepad_state.thumbsticks[1].vertical;
    state.thumbsticks.right.horizontal = hid_gamepad_state.thumbsticks[1].horizontal;

    err = k_msgq_put(&hids_queue, &state, K_NO_WAIT);
    if (err)
    {
        printk("No space in the queue for gamepad event\n");
        return err;
    }
    if (k_msgq_num_used_get(&hids_queue) >= 1)
    {
        k_work_submit_to_queue(&hids_work_q, &hids_work);
    }

    return 0;
}

static void button_changed(uint32_t button_state, uint32_t has_changed)
{
    static bool pairing_button_pressed;

    uint32_t buttons = button_state & has_changed;

    if (k_msgq_num_used_get(&mitm_queue))
    {
        if (buttons & KEY_PAIRING_ACCEPT)
        {
            pairing_button_pressed = true;
            num_comp_reply_value = 1;
            k_work_submit(&num_comp_reply_work);

            return;
        }

        if (buttons & KEY_PAIRING_REJECT)
        {
            pairing_button_pressed = true;
            num_comp_reply_value = 0;
            k_work_submit(&num_comp_reply_work);

            return;
        }
    }

    data_to_send = false;

    // Button mapping in accordance with W3C (World Wide Web Consortium)
    if (has_changed & BUTTON_X_MASK)
        gamepad_button_changed(0, (button_state & BUTTON_X_MASK) != 0);
    if (has_changed & BUTTON_Y_MASK)
        gamepad_button_changed(1, (button_state & BUTTON_Y_MASK) != 0);
    if (has_changed & BUTTON_A_MASK)
        gamepad_button_changed(2, (button_state & BUTTON_A_MASK) != 0);
    if (has_changed & BUTTON_B_MASK)
        gamepad_button_changed(3, (button_state & BUTTON_B_MASK) != 0);

    if (has_changed & BUTTON_DOWN_MASK)
        gamepad_button_changed(13, (button_state & BUTTON_DOWN_MASK) != 0);
    if (has_changed & BUTTON_RIGHT_MASK)
        gamepad_button_changed(15, (button_state & BUTTON_RIGHT_MASK) != 0);
    if (has_changed & BUTTON_LEFT_MASK)
        gamepad_button_changed(14, (button_state & BUTTON_LEFT_MASK) != 0);
    if (has_changed & BUTTON_UP_MASK)
        gamepad_button_changed(12, (button_state & BUTTON_UP_MASK) != 0);

    if (has_changed & BUTTON_LEFT_TRIGGER_BUTTON_MASK)
        gamepad_button_changed(6, (button_state & BUTTON_LEFT_TRIGGER_BUTTON_MASK) != 0);
    if (has_changed & BUTTON_LEFT_BUMPER_MASK)
        gamepad_button_changed(4, (button_state & BUTTON_LEFT_BUMPER_MASK) != 0);

    if (has_changed & BUTTON_RIGHT_TRIGGER_BUTTON_MASK)
        gamepad_button_changed(7, (button_state & BUTTON_RIGHT_TRIGGER_BUTTON_MASK) != 0);
    if (has_changed & BUTTON_RIGHT_BUMPER_MASK)
        gamepad_button_changed(5, (button_state & BUTTON_RIGHT_BUMPER_MASK) != 0);

    if (has_changed & BUTTON_LEFT_STICK_BUTTON_MASK)
        gamepad_button_changed(10, (button_state & BUTTON_LEFT_STICK_BUTTON_MASK) != 0);
    if (has_changed & BUTTON_RIGHT_STICK_BUTTON_MASK)
        gamepad_button_changed(11, (button_state & BUTTON_RIGHT_STICK_BUTTON_MASK) != 0);

    if (has_changed & BUTTON_MINUS_MASK)
        gamepad_button_changed(8, (button_state & BUTTON_MINUS_MASK) != 0);
    if (has_changed & BUTTON_PLUS_MASK)
        gamepad_button_changed(9, (button_state & BUTTON_PLUS_MASK) != 0);


    if (data_to_send)
        add_to_queue();
}

static int saadc_sample(void)
{
    int ret;
    const struct adc_sequence sequence = {
        .channels = 15,
        .buffer = saadc_buffer,
        .buffer_size = sizeof(saadc_buffer),
        .resolution = ADC_RESOLUTION,
    };

    if (!adc_dev)
    {
        return -1;
    }

    ret = adc_read(adc_dev, &sequence);
    if (ret)
    {
        printk("adc_read() failed with code %d\n", ret);
    }

    gamepad_thumbstick_changed(0, saadc_buffer[0] >= 0 ? saadc_buffer[0] : 0, saadc_buffer[1] >= 0 ? saadc_buffer[1] : 0);
    gamepad_thumbstick_changed(1, saadc_buffer[2] >= 0 ? saadc_buffer[2] : 0, saadc_buffer[3] >= 0 ? saadc_buffer[3] : 0);

    if (data_to_send)
        add_to_queue();

    return ret;
}

static void saadc_handler(struct k_work *work)
{
    saadc_sample();
}

void adc_sample_event(struct k_timer *timer_id)
{
    k_work_submit_to_queue(&saadc_work_q, &saadc_work);
}

void configure_saadc(void)
{
    int err;

    k_timer_init(&saadc_timer, adc_sample_event, NULL);
    k_timer_start(&saadc_timer, K_MSEC(SAADC_INTERVAL_MSEC), K_MSEC(SAADC_INTERVAL_MSEC));

    adc_dev = device_get_binding(ADC_DEVICE_NAME);
    if (!adc_dev)
    {
        printk("device_get_binding ADC_0 (=%s) failed\n", ADC_DEVICE_NAME);
    }

    for (int i = 0; i < 4; i++)
    {
        const struct adc_channel_cfg saadc_channel_cfg = {
            .gain = ADC_GAIN,
            .reference = ADC_REFERENCE,
            .acquisition_time = ADC_ACQUISITION_TIME,
            .channel_id = i,
            .input_positive = saadc_inputs[i]};

        err = adc_channel_setup(adc_dev, &saadc_channel_cfg);
        if (err)
        {
            printk("Error in adc channel %d setup: %d\n", i, err);
        }
    }
}

void button_pressed(const struct device *dev, struct gpio_callback *cb, uint32_t pins)
{
        int ret = 0;

	uint32_t pin_mask = 0;
        gpio_port_value_t pin_values;
        for (int i = 0; i < 32; i++)
        {
            if (pins & (1 << i))
            {
                ret = gpio_port_get_raw(dev, &pin_values);
            }
        }
        button_changed(~pin_values, pins);
}

void configure_gpio(void) 
{
    int ret;

    gpio_port_pins_t pin_mask = 0;
    for (int i = 0; i < 16; i++) {
        pin_mask |= BIT(button[i].pin);
        ret = gpio_pin_configure_dt(&button[i], GPIO_INPUT);
        ret = gpio_pin_interrupt_configure_dt(&button[i], GPIO_INT_EDGE_BOTH);
    }
    gpio_init_callback(&button_cb_data, button_pressed, pin_mask);
    gpio_add_callback(button[0].port, &button_cb_data);

    for (int i = 0; i < 2; i++)
        ret = gpio_pin_configure_dt(&led[i], GPIO_OUTPUT);
}


void main(void)
{
    int err;
    int blink_status = 0;

    printk("Initializing BLE HID Gamepad\n");

    configure_gpio();
    configure_saadc();

    bt_conn_cb_register(&conn_callbacks);
    bt_conn_auth_cb_register(&conn_auth_callbacks);

    err = bt_enable(NULL);
    if (err)
    {
        printk("Bluetooth init failed (err %d)\n", err);
        return;
    }

    printk("Bluetooth initialized\n");

    hid_init();

    k_work_queue_start(&hids_work_q, hids_stack, K_THREAD_STACK_SIZEOF(hids_stack), HIDS_PRIORITY, NULL);
    k_work_init(&hids_work, gamepad_event_handler);
    
    k_work_queue_start(&saadc_work_q, saadc_stack, K_THREAD_STACK_SIZEOF(saadc_stack), SAADC_PRIORITY, NULL);
    k_work_init(&saadc_work, saadc_handler);

    k_work_init(&pairing_work, pairing_process);
    k_work_init(&num_comp_reply_work, num_comp_reply_handler);

    if (IS_ENABLED(CONFIG_SETTINGS))
    {
        settings_load();
    }

    advertising_start();

    for (;;)
    {
        if (is_adv)
        {
            gpio_pin_set_raw(led[0].port, ADV_STATUS_LED, (++blink_status) % 2);
            printk("Blink_status: %d\n", blink_status % 2);
        }
        else
        {
            gpio_pin_set_raw(led[0].port, ADV_STATUS_LED, 0);
        }
        k_sleep(K_MSEC(ADV_LED_BLINK_INTERVAL));
    }
}
