// -------- 7-seg pins --------
int a = 7, b = 6, c = 5, d = 11, e = 10, f = 8, g = 9;
/*
g: top-left
f: mid
b: top-right
*/

// -------- IO pins --------
int potPin = A0;
int redPin = 4;
int yellowPin = 3;
int greenPin = 2; // uses TX pin on UNO; keep Serial OFF
int buzzerPin = 13;
int buttonPin = 12;

// -------- defaults (secs) --------
int redSec = 3;
int yellowSec = 2;
int greenSec = 5;

// -------- state --------
#define MODE_RUN    0
#define MODE_CONFIG 1

#define LIGHT_GREEN 0
#define LIGHT_YELLOW 1
#define LIGHT_RED   2

int mode = MODE_RUN;
int currentLight = LIGHT_GREEN;
int configLight = LIGHT_GREEN;
int secondsLeft = 0;

// -------- timekeeping --------
unsigned long lastTickMs = 0; // 1 Hz countdown
unsigned long lastBlinkMs = 0; // 1 Hz toggle
bool blinkPhase = true;

bool lastBtn = HIGH; // INPUT_PULLUP
unsigned long pressStart = 0;

// -------- 7-seg helpers --------
void clearDisplay() {
	int s[] = {a, b, c, d, e, f, g};
	for (int i = 0; i < 8; i++) digitalWrite(s[i], LOW);
}

void segOn(int segs[], int n) {
	for (int i = 0; i < n; i++) digitalWrite(segs[i], HIGH);
}

void display0() {
	int s[] = {a, b, c, d, e, f};
	segOn(s, 6);
}

void display1() {
	int s[] = {b, c};
	segOn(s, 2);
}

void display2() {
	int s[] = {a, b, g, e, d};
	segOn(s, 5);
}

void display3() {
	int s[] = {a, b, c, d, g};
	segOn(s, 5);
}

void display4() {
	int s[] = {f, b, g, c};
	segOn(s, 4);
}

void display5() {
	int s[] = {a, f, g, c, d};
	segOn(s, 5);
}

void display6() {
	int s[] = {a, f, g, c, d, e};
	segOn(s, 6);
}

void display7() {
	int s[] = {a, b, c};
	segOn(s, 3);
}

void display8() {
	int s[] = {a, b, c, d, e, f, g};
	segOn(s, 7);
}

void display9() {
	int s[] = {a, b, c, d, f, g};
	segOn(s, 6);
}

void (*digits[])() = {
	display0, display1, display2, display3, display4, display5, display6, display7, display8, display9
};

void showDigit(int v) {
	if (v < 0)v = 0;
	if (v > 9)v = 9;
	clearDisplay();
	digits[v]();
}

// -------- light helpers --------
void lightsOff() {
	digitalWrite(redPin, LOW);
	digitalWrite(yellowPin, LOW);
	digitalWrite(greenPin, LOW);
}

void lightOn(int l) {
	lightsOff();
	if (l == LIGHT_GREEN) digitalWrite(greenPin, HIGH);
	else if (l == LIGHT_YELLOW) digitalWrite(yellowPin, HIGH);
	else digitalWrite(redPin, HIGH);
}

int getTimeFor(int l) {
	switch (l) {
	case LIGHT_GREEN: return greenSec;
	case LIGHT_YELLOW: return yellowSec;
	default: return redSec;
	}
}

void setTimeFor(int l, int v) {
	switch (l) {
	case LIGHT_GREEN: greenSec = v;
		break;
	case LIGHT_YELLOW: yellowSec = v;
		break;
	default: redSec = v;
		break;
	}
}

int nextLight(int l) { return (l + 1) % 3; }

// -------- buzzer --------
void beepOnce(int dur = 120) {
	tone(buzzerPin, 1200, dur);
	delay(dur + 20);
}

void beepTriple() {
	for (int i = 0; i < 3; i++) {
		tone(buzzerPin, 1000, 100);
		delay(140);
	}
}

// -------- inputs --------
int potToDigit() {
	int v = analogRead(potPin);
	return v * 10 / 1024;
} // 0..9

void enterRunMode() {
	mode = MODE_RUN;
	secondsLeft = getTimeFor(currentLight);
	lightOn(currentLight);
	showDigit(secondsLeft);
	lastTickMs = millis();
}

void enterConfigMode() {
	mode = MODE_CONFIG;
	configLight = LIGHT_GREEN;
	blinkPhase = true;
	lastBlinkMs = millis();
	lightsOff();
	showDigit(getTimeFor(configLight));
}

void setup() {
	Serial.begin(9600);
	{
		int s[] = {a, b, c, d, e, f, g};
		for (int i = 0; i < 8; i++) pinMode(s[i], OUTPUT);
	}
	pinMode(redPin, OUTPUT);
	pinMode(yellowPin, OUTPUT);
	pinMode(greenPin, OUTPUT);

	pinMode(buzzerPin, OUTPUT);
	pinMode(buttonPin, INPUT);

	clearDisplay();
	currentLight = LIGHT_GREEN;
	secondsLeft = getTimeFor(currentLight);
	lightOn(currentLight);
	showDigit(secondsLeft);
	lastTickMs = millis();
	lastBlinkMs = millis();
	lastBtn = digitalRead(buttonPin);
}

#define HOLD_MS 5000 // 5s hold to switch mode

void loop() {
	unsigned long now = millis();
	int btnRaw = digitalRead(buttonPin);
	if (btnRaw == HIGH) {
		pressStart = now;
		while (digitalRead(buttonPin) == HIGH);
		unsigned long heldTime = millis() - pressStart;
		Serial.println(heldTime);
		if (heldTime >= HOLD_MS) {
			if (mode == MODE_RUN) {
				Serial.println("Config mode");
				enterConfigMode();
			} else {
				Serial.println("Run mode");
				enterRunMode();
			}
		} else {
			if (mode == MODE_CONFIG) {
				int val = potToDigit(); // 0..9
				if (val == 0) {
					beepTriple(); // reject zero
				} else {
					setTimeFor(configLight, val); // save
					beepOnce(); // confirm
					configLight = nextLight(configLight);
					blinkPhase = true;
					lastBlinkMs = now;
					lightsOff();
					showDigit(getTimeFor(configLight));
				}
			}
		}
	}

	// ---- Main behaviors (unchanged) ----
	if (mode == MODE_RUN) {
		if (now - lastTickMs >= 1000) {
			lastTickMs = now;
			if (secondsLeft > 0) secondsLeft--;
			showDigit(secondsLeft);
			if (secondsLeft == 0) {
				currentLight = nextLight(currentLight);
				secondsLeft = getTimeFor(currentLight);
				lightOn(currentLight);
				showDigit(secondsLeft);
			}
		}
	} else { // MODE_CONFIG
		if (now - lastBlinkMs >= 1000) {
			lastBlinkMs = now;
			blinkPhase = !blinkPhase;
		}
		if (blinkPhase) {
			int cand = potToDigit(); // live preview 0..9
			showDigit(cand);
			lightsOff();
		} else {
			clearDisplay();
			lightOn(configLight);
		}
	}

	delay(2); // tiny jitter padding
}