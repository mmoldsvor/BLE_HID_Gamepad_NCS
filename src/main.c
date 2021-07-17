#include <zephyr/types.h>
#include <stddef.h>
#include <string.h>
#include <errno.h>
#include <sys/printk.h>
#include <sys/byteorder.h>
#include <zephyr.h>
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

#include <bluetooth/services/bas.h>
#include <bluetooth/services/hids.h>
#include <bluetooth/services/dis.h>
#include <dk_buttons_and_leds.h>

#define DEVICE_NAME     CONFIG_BT_DEVICE_NAME
#define DEVICE_NAME_LEN (sizeof(DEVICE_NAME) - 1)

#define BASE_USB_HID_SPEC_VERSION   0x0101

#define OUTPUT_REPORT_MAX_LEN                1
#define OUTPUT_REPORT_BIT_MASK_CAPS_LOCK     0x02
#define OUTPUT_REP_KEYS_REF_ID               1
#define INPUT_REP_GAMEPAD_BUTTONS_REF_ID     1
#define INPUT_REP_GAMEPAD_LEFT_STICK_REF_ID  2
#define INPUT_REP_GAMEPAD_RIGHT_STICK_REF_ID 3
#define MODIFIER_KEY_POS                     0
#define SHIFT_KEY_CODE                       0x02
#define SCAN_CODE_POS                        2
#define KEYS_MAX_LEN                         (INPUT_REPORT_KEYS_MAX_LEN - SCAN_CODE_POS)

#define ADV_LED_BLINK_INTERVAL  1000

#define ADV_STATUS_LED DK_LED1
#define CON_STATUS_LED DK_LED2
#define LED_CAPS_LOCK  DK_LED3
#define NFC_LED	       DK_LED4

#define BUTTON_A_MASK       DK_BTN1_MSK
#define BUTTON_B_MASK       DK_BTN2_MSK
#define BUTTON_X_MASK       DK_BTN3_MSK
#define BUTTON_Y_MASK       DK_BTN4_MSK

#define BUTTON_DOWN_MASK    DK_BTN1_MSK
#define BUTTON_RIGHT_MASK   DK_BTN2_MSK
#define BUTTON_LEFT_MASK    DK_BTN3_MSK
#define BUTTON_UP_MASK      DK_BTN4_MSK

#define KEY_ADV_MASK        DK_BTN4_MSK

/* Key used to accept or reject passkey value */
#define KEY_PAIRING_ACCEPT DK_BTN1_MSK
#define KEY_PAIRING_REJECT DK_BTN2_MSK

/* HIDs queue elements. */
#define HIDS_QUEUE_SIZE 10

#define INPUT_REPORT_GAMEPAD_BUTTONS_MAX_LEN 2
#define INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN 2


/* OUT report internal indexes.
 *
 * This is a position in internal report table and is not related to
 * report ID.
 */
enum {
	OUTPUT_REP_KEYS_IDX = 0
};

/* INPUT report internal indexes.
 *
 * This is a position in internal report table and is not related to
 * report ID.
 */
enum {
	INPUT_REP_GAMEPAD_BUTTONS_IDX = 0,
    INPUT_REP_GAMEPAD_LEFT_STICK_IDX,
    INPUT_REP_GAMEPAD_RIGHT_STICK_IDX
};

/* HIDS instance. */
BT_HIDS_DEF(hids_obj,
	    OUTPUT_REPORT_MAX_LEN,
	    INPUT_REPORT_GAMEPAD_BUTTONS_MAX_LEN + 2*INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN);  // Verify that this is the sum of all max lengths and not the largest report

static volatile bool is_adv;

static const struct bt_data ad[] = {
	BT_DATA_BYTES(BT_DATA_GAP_APPEARANCE,
		      (CONFIG_BT_DEVICE_APPEARANCE >> 0) & 0xff,
		      (CONFIG_BT_DEVICE_APPEARANCE >> 8) & 0xff),
	BT_DATA_BYTES(BT_DATA_FLAGS, (BT_LE_AD_GENERAL | BT_LE_AD_NO_BREDR)),
	BT_DATA_BYTES(BT_DATA_UUID16_ALL,
		      0x12, 0x18,       /* HID Service */
		      0x0f, 0x18),      /* Battery Service */

};

static const struct bt_data sd[] = {
	BT_DATA(BT_DATA_NAME_COMPLETE, DEVICE_NAME, DEVICE_NAME_LEN),
};

static struct conn_mode {
	struct bt_conn *conn;
} conn_mode[CONFIG_BT_HIDS_MAX_CLIENT_COUNT];

typedef struct {
    uint8_t horizontal;
    uint8_t vertical;
} thumbstick_state;

static struct gamepad_state {
    bool buttons[16];
    thumbstick_state thumbsticks[2];
    bool thumbstick_temp_buttons[4];
} hid_gamepad_state;

static struct k_work pairing_work;
struct pairing_data_mitm {
	struct bt_conn *conn;
	unsigned int passkey;
};

K_MSGQ_DEFINE(mitm_queue,
	      sizeof(struct pairing_data_mitm),
	      CONFIG_BT_HIDS_MAX_CLIENT_COUNT,
	      4);

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
	if (err) {
		if (err == -EALREADY) {
			printk("Advertising continued\n");
		} else {
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
	if (err) {
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

	if (err) {
		printk("Failed to connect to %s (%u)\n", addr, err);
		return;
	}

	printk("Connected %s\n", addr);
	dk_set_led_on(CON_STATUS_LED);

	err = bt_hids_connected(&hids_obj, conn);

	if (err) {
		printk("Failed to notify HID service about connection\n");
		return;
	}

	for (size_t i = 0; i < CONFIG_BT_HIDS_MAX_CLIENT_COUNT; i++) {
		if (!conn_mode[i].conn) {
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

	if (err) {
		printk("Failed to notify HID service about disconnection\n");
	}

	for (size_t i = 0; i < CONFIG_BT_HIDS_MAX_CLIENT_COUNT; i++) {
		if (conn_mode[i].conn == conn) {
			conn_mode[i].conn = NULL;
		} else {
			if (conn_mode[i].conn) {
				is_any_dev_connected = true;
			}
		}
	}

	if (!is_any_dev_connected) {
		dk_set_led_off(CON_STATUS_LED);
	}

	advertising_start();
}


static void security_changed(struct bt_conn *conn, bt_security_t level,
			     enum bt_security_err err)
{
	char addr[BT_ADDR_LE_STR_LEN];

	bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

	if (!err) {
		printk("Security changed: %s level %u\n", addr, level);
	} else {
		printk("Security failed: %s level %u err %d\n", addr, level,
			err);
	}
}


static struct bt_conn_cb conn_callbacks = {
	.connected = connected,
	.disconnected = disconnected,
	.security_changed = security_changed,
};


static void caps_lock_handler(const struct bt_hids_rep *rep)
{
	uint8_t report_val = ((*rep->data) & OUTPUT_REPORT_BIT_MASK_CAPS_LOCK) ?
			  1 : 0;
	dk_set_led(LED_CAPS_LOCK, report_val);
}


static void hids_outp_rep_handler(struct bt_hids_rep *rep,
				  struct bt_conn *conn,
				  bool write)
{
	char addr[BT_ADDR_LE_STR_LEN];

	if (!write) {
		printk("Output report read\n");
		return;
	};

	bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));
	printk("Output report has been received %s\n", addr);
	caps_lock_handler(rep);
}


static void hids_boot_kb_outp_rep_handler(struct bt_hids_rep *rep,
					  struct bt_conn *conn,
					  bool write)
{
	char addr[BT_ADDR_LE_STR_LEN];

	if (!write) {
		printk("Output report read\n");
		return;
	};

	bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));
	printk("Boot Keyboard Output report has been received %s\n", addr);
	caps_lock_handler(rep);
}


static void hids_pm_evt_handler(enum bt_hids_pm_evt evt,
				struct bt_conn *conn)
{
	char addr[BT_ADDR_LE_STR_LEN];
	size_t i;

	for (i = 0; i < CONFIG_BT_HIDS_MAX_CLIENT_COUNT; i++) {
		if (conn_mode[i].conn == conn) {
			break;
		}
	}

	if (i >= CONFIG_BT_HIDS_MAX_CLIENT_COUNT) {
		printk("Cannot find connection handle when processing PM");
		return;
	}

	bt_addr_le_to_str(bt_conn_get_dst(conn), addr, sizeof(addr));

	switch (evt) {
	case BT_HIDS_PM_EVT_BOOT_MODE_ENTERED:
		printk("Boot mode entered %s\n", addr);
		break;

	case BT_HIDS_PM_EVT_REPORT_MODE_ENTERED:
		printk("Report mode entered %s\n", addr);
		break;

	default:
		break;
	}
}


static void hid_init(void)
{
	int err;
	struct bt_hids_init_param    hids_init_obj = { 0 };
	struct bt_hids_inp_rep       *hids_inp_rep;
	struct bt_hids_outp_feat_rep *hids_outp_rep;

	static const uint8_t report_map[] = {
		0x05, 0x01,                    // USAGE_PAGE (Generic Desktop)
        0x09, 0x05,                    // USAGE (Game Pad)
        0xa1, 0x01,                    // COLLECTION (Application)
        0x85, 0x01,                    //   REPORT_ID (1)
        0x09, 0x01,                    //   USAGE (Pointer)
        0xa1, 0x00,                    //   COLLECTION (Physical)
        0x05, 0x09,                    //     USAGE_PAGE (Button)
        0x95, 0x10,                    //     REPORT_COUNT (16)
        0x75, 0x01,                    //     REPORT_SIZE (1)
        0x19, 0x01,                    //     USAGE_MINIMUM (Button 1)
        0x29, 0x10,                    //     USAGE_MAXIMUM (Button 16)
        0x15, 0x00,                    //     LOGICAL_MINIMUM (0)
        0x25, 0x01,                    //     LOGICAL_MAXIMUM (1)
        0x81, 0x02,                    //     INPUT (Data,Var,Abs)
        0xc0,                          //   END_COLLECTION
        0x85, 0x02,                    //   REPORT_ID (2)
        0x05, 0x01,                    //   USAGE_PAGE (Generic Desktop)
        0x09, 0x01,                    //   USAGE (Pointer)
        0xa1, 0x00,                    //   COLLECTION (Physical)
        0x75, 0x08,                    //     REPORT_SIZE (8)
        0x95, 0x02,                    //     REPORT_COUNT (2)
        0x09, 0x30,                    //     USAGE (X)
        0x09, 0x31,                    //     USAGE (Y)
        0x15, 0x00,                    //     LOGICAL_MINIMUM (0)
        0x26, 0xff, 0x00,              //     LOGICAL_MAXIMUM (255)
        0x81, 0x02,                    //     INPUT (Data,Var,Abs)
        0xc0,                          //   END_COLLECTION
        0x85, 0x03,                    //   REPORT_ID (3)
        0x09, 0x01,                    //   USAGE (Pointer)
        0xa1, 0x00,                    //   COLLECTION (Physical)
        0x75, 0x08,                    //     REPORT_SIZE (8)
        0x95, 0x02,                    //     REPORT_COUNT (2)
        0x09, 0x32,                    //     USAGE (Z)
        0x09, 0x33,                    //     USAGE (Rx)
        0x15, 0x00,                    //     LOGICAL_MINIMUM (0)
        0x26, 0xff, 0x00,              //     LOGICAL_MAXIMUM (255)
        0x81, 0x02,                    //     INPUT (Data,Var,Abs)
        0xc0,                          //   END_COLLECTION
        0xc0                           // END_COLLECTION
	};

	hids_init_obj.rep_map.data = report_map;
	hids_init_obj.rep_map.size = sizeof(report_map);

	hids_init_obj.info.bcd_hid = BASE_USB_HID_SPEC_VERSION;
	hids_init_obj.info.b_country_code = 0x00;
	hids_init_obj.info.flags = (BT_HIDS_REMOTE_WAKE | BT_HIDS_NORMALLY_CONNECTABLE);

	hids_inp_rep = &hids_init_obj.inp_rep_group_init.reports[INPUT_REP_GAMEPAD_BUTTONS_IDX];
	hids_inp_rep->size = INPUT_REPORT_GAMEPAD_BUTTONS_MAX_LEN;
	hids_inp_rep->id = INPUT_REP_GAMEPAD_BUTTONS_REF_ID;
	hids_init_obj.inp_rep_group_init.cnt++;

    hids_inp_rep = &hids_init_obj.inp_rep_group_init.reports[INPUT_REP_GAMEPAD_LEFT_STICK_IDX];
    hids_inp_rep->size = INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN;
    hids_inp_rep->id = INPUT_REP_GAMEPAD_LEFT_STICK_REF_ID;
    hids_init_obj.inp_rep_group_init.cnt++;

    hids_inp_rep = &hids_init_obj.inp_rep_group_init.reports[INPUT_REP_GAMEPAD_RIGHT_STICK_IDX];
    hids_inp_rep->size = INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN;
    hids_inp_rep->id = INPUT_REP_GAMEPAD_RIGHT_STICK_REF_ID;
    hids_init_obj.inp_rep_group_init.cnt++;

	hids_outp_rep = &hids_init_obj.outp_rep_group_init.reports[OUTPUT_REP_KEYS_IDX];
	hids_outp_rep->size = OUTPUT_REPORT_MAX_LEN;
	hids_outp_rep->id = OUTPUT_REP_KEYS_REF_ID;
	hids_outp_rep->handler = hids_outp_rep_handler;
	hids_init_obj.outp_rep_group_init.cnt++;

	hids_init_obj.is_kb = true;
	hids_init_obj.boot_kb_outp_rep_handler = hids_boot_kb_outp_rep_handler;
	hids_init_obj.pm_evt_handler = hids_pm_evt_handler;

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

	pairing_data.conn    = bt_conn_ref(conn);
	pairing_data.passkey = passkey;

	err = k_msgq_put(&mitm_queue, &pairing_data, K_NO_WAIT);
	if (err) {
		printk("Pairing queue is full. Purge previous data.\n");
	}

	/* In the case of multiple pairing requests, trigger
	 * pairing confirmation which needed user interaction only
	 * once to avoid display information about all devices at
	 * the same time. Passkey confirmation for next devices will
	 * be proccess from queue after handling the earlier ones.
	 */
	if (k_msgq_num_used_get(&mitm_queue) == 1) {
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

	if (k_msgq_peek(&mitm_queue, &pairing_data) != 0) {
		return;
	}

	if (pairing_data.conn == conn) {
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
	.pairing_failed = pairing_failed
};


static int gamepad_report_button_send(const struct gamepad_state *state, struct bt_conn *conn)
{
    int err = 0;
    uint8_t data[INPUT_REPORT_GAMEPAD_BUTTONS_MAX_LEN] = {0};

    for (int i = 0; i < 8; i++) {
        data[0] = data[0] + (state->buttons[i] << i);
        data[1] = data[1] + (state->buttons[i+8] << i);
    }
    err = bt_hids_inp_rep_send(&hids_obj, conn, INPUT_REP_GAMEPAD_BUTTONS_IDX, data, sizeof(data), NULL);

    return err;
}

static int gamepad_report_thumbstick_send(const struct gamepad_state *state, struct bt_conn *conn, uint8_t thumbstick)
{
    int err = 0;
    uint8_t data[INPUT_REPORT_GAMEPAD_THUMBSTICK_MAX_LEN];

    data[0] = state->thumbsticks[thumbstick].horizontal;
    data[1] = state->thumbsticks[thumbstick].vertical;

    err = bt_hids_inp_rep_send(&hids_obj, conn, INPUT_REP_GAMEPAD_LEFT_STICK_IDX + thumbstick, data, sizeof(data), NULL);

    return err;
}


static int button_report_send(void)
{
    for (size_t i = 0; i < CONFIG_BT_HIDS_MAX_CLIENT_COUNT; i++) {
        if (conn_mode[i].conn) {
            int err;

            err = gamepad_report_button_send(&hid_gamepad_state, conn_mode[i].conn);

            if (err) {
                printk("Button report send error: %d\n", err);
                return err;
            }
        }
    }
    return 0;
}

static int thumbstick_report_send(uint8_t thumbstick)
{
    for (size_t i = 0; i < CONFIG_BT_HIDS_MAX_CLIENT_COUNT; i++) {
        if (conn_mode[i].conn) {
            int err;
             
            err = gamepad_report_thumbstick_send(&hid_gamepad_state, conn_mode[i].conn, thumbstick);

            if (err) {
                printk("Thumbstick report send error: %d\n", err);
                return err;
            }
        }
    }
    return 0;
}


static int gamepad_button_changed(uint8_t button, bool down)
{
    hid_gamepad_state.buttons[button] = down;
    return button_report_send();
}

static int gamepad_thumbstick_changed(uint8_t thumbstick, uint8_t horizontal, uint8_t vertical)
{
    hid_gamepad_state.thumbsticks[thumbstick].horizontal = horizontal;
    hid_gamepad_state.thumbsticks[thumbstick].vertical = vertical;
    return thumbstick_report_send(thumbstick);
}

static int gamepad_thumbstick_changed_temp(uint8_t thumbstick, uint8_t button, bool down)
{
    hid_gamepad_state.thumbstick_temp_buttons[button] = down;

    uint8_t horizontal = 127;
    uint8_t vertical = 127;
    if (hid_gamepad_state.thumbstick_temp_buttons[0] != hid_gamepad_state.thumbstick_temp_buttons[2]) {
        horizontal = hid_gamepad_state.thumbstick_temp_buttons[0]*255;
    }
    if (hid_gamepad_state.thumbstick_temp_buttons[1] != hid_gamepad_state.thumbstick_temp_buttons[3]) {
        vertical = hid_gamepad_state.thumbstick_temp_buttons[1]*255;
    }

    return gamepad_thumbstick_changed(thumbstick, horizontal, vertical);
}

static void num_comp_reply(bool accept)
{
	struct pairing_data_mitm pairing_data;
	struct bt_conn *conn;

	if (k_msgq_get(&mitm_queue, &pairing_data, K_NO_WAIT) != 0) {
		return;
	}

	conn = pairing_data.conn;

	if (accept) {
		bt_conn_auth_passkey_confirm(conn);
		printk("Numeric Match, conn %p\n", conn);
	} else {
		bt_conn_auth_cancel(conn);
		printk("Numeric Reject, conn %p\n", conn);
	}

	bt_conn_unref(pairing_data.conn);

	if (k_msgq_num_used_get(&mitm_queue)) {
		k_work_submit(&pairing_work);
	}
}


static void button_changed(uint32_t button_state, uint32_t has_changed)
{
    static bool pairing_button_pressed;

    uint32_t buttons = button_state & has_changed;

    if (k_msgq_num_used_get(&mitm_queue)) {
        if (buttons & KEY_PAIRING_ACCEPT) {
			pairing_button_pressed = true;
			num_comp_reply(true);

			return;
		}

		if (buttons & KEY_PAIRING_REJECT) {
			pairing_button_pressed = true;
			num_comp_reply(false);

			return;
		}
    }
        
    for (int thumbstick = 0; thumbstick < 2; thumbstick++)
    {
        if (has_changed & BUTTON_A_MASK)
            gamepad_thumbstick_changed_temp(thumbstick, 0, (button_state & BUTTON_A_MASK) != 0);
        if (has_changed & BUTTON_B_MASK)
            gamepad_thumbstick_changed_temp(thumbstick, 1, (button_state & BUTTON_B_MASK) != 0);
        if (has_changed & BUTTON_X_MASK)
            gamepad_thumbstick_changed_temp(thumbstick, 2, (button_state & BUTTON_X_MASK) != 0);
        if (has_changed & BUTTON_Y_MASK)
            gamepad_thumbstick_changed_temp(thumbstick, 3, (button_state & BUTTON_Y_MASK) != 0);
    }

    if (has_changed & BUTTON_A_MASK)
        gamepad_button_changed(0, (button_state & BUTTON_A_MASK) != 0);
    if (has_changed & BUTTON_B_MASK)
        gamepad_button_changed(1, (button_state & BUTTON_B_MASK) != 0);
    if (has_changed & BUTTON_X_MASK)
        gamepad_button_changed(2, (button_state & BUTTON_X_MASK) != 0);
    if (has_changed & BUTTON_Y_MASK)
        gamepad_button_changed(3, (button_state & BUTTON_Y_MASK) != 0);

    if (has_changed & BUTTON_DOWN_MASK)
        gamepad_button_changed(13, (button_state & BUTTON_DOWN_MASK) != 0);
    if (has_changed & BUTTON_RIGHT_MASK)
        gamepad_button_changed(15, (button_state & BUTTON_RIGHT_MASK) != 0);
    if (has_changed & BUTTON_LEFT_MASK)
        gamepad_button_changed(14, (button_state & BUTTON_LEFT_MASK) != 0);
    if (has_changed & BUTTON_UP_MASK)
        gamepad_button_changed(12, (button_state & BUTTON_UP_MASK) != 0);
}


static void configure_gpio(void)
{
	int err;

	err = dk_buttons_init(button_changed);
	if (err) {
		printk("Cannot init buttons (err: %d)\n", err);
	}

	err = dk_leds_init();
	if (err) {
		printk("Cannot init LEDs (err: %d)\n", err);
	}
}


static void bas_notify(void)
{
	uint8_t battery_level = bt_bas_get_battery_level();

	battery_level--;

	if (!battery_level) {
		battery_level = 100U;
	}

	bt_bas_set_battery_level(battery_level);
}


void main(void)
{
	int err;
	int blink_status = 0;

	printk("Initializing BLE HID Gamepad\n");

	configure_gpio();

	bt_conn_cb_register(&conn_callbacks);
	bt_conn_auth_cb_register(&conn_auth_callbacks);

	err = bt_enable(NULL);
	if (err) {
		printk("Bluetooth init failed (err %d)\n", err);
		return;
	}

	printk("Bluetooth initialized\n");

	hid_init();

	if (IS_ENABLED(CONFIG_SETTINGS)) {
		settings_load();
	}

	advertising_start();

	k_work_init(&pairing_work, pairing_process);

	for (;;) {
		if (is_adv) {
			dk_set_led(ADV_STATUS_LED, (++blink_status) % 2);
		} else {
			dk_set_led_off(ADV_STATUS_LED);
		}
		k_sleep(K_MSEC(ADV_LED_BLINK_INTERVAL));
		/* Battery level simulation */
		bas_notify();
	}
}