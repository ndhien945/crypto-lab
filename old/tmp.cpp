// 7-seg pins
int a = 8, b = 7, c = 6, d = 12, e = 11, f = 9, g = 10;
/*
g: top-left
f: mid-mid
a: top-mid
b: top-right
e: bot-left
d: bot-mid
c: bot-left
*/

int potPin = A0;
int redPin = 4;
int yellowPin = 3;
int greenPin = 2;
int buzzerPin = 5;
int buttonPin = 13;

// light default secs
int greenSec = 5;
int yellowSec = 2;
int redSec = 3;

// mode and light state
#define MODE_RUN    0
#define MODE_CONFIG 1

#define LIGHT_GREEN 0
#define LIGHT_YELLOW 1
#define LIGHT_RED   2

int mode = MODE_RUN;
int currentLight = LIGHT_GREEN;
int configLight = LIGHT_GREEN;
int secondsLeft = 0;

unsigned long lastTickMs = 0;
unsigned long lastBlinkMs = 0;
bool blinkPhase = true;

bool lastBtn = HIGH;
unsigned long pressStart = 0;

// 7-seg helper funcs
void clearDisplay() {
	int s[] = {a, b, c, d, e, f, g};
	for (int i = 0; i < 7; i++) digitalWrite(s[i], LOW);
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

// light funcs
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
		case LIGHT_GREEN: greenSec = v; break;
		case LIGHT_YELLOW: yellowSec = v; break;
		default: redSec = v; break;
	}
}

int nextLight(int l) { return (l + 1) % 3; }

// buzzer
void beepOnce() {
	tone(buzzerPin, 1200, 100);
 	delay(140);
}

void beepTriple() {
	for (int i = 0; i < 3; i++) {
		tone(buzzerPin, 1000, 100);
		delay(140);
	}
}

// potentiometer, map to 0-9
int potToDigit() {
	int v = analogRead(potPin);
	return v * 10 / 1024;
}

void enterRunMode() {
	mode = MODE_RUN;
	currentLight = LIGHT_GREEN;
	secondsLeft = getTimeFor(currentLight);
	lightOn(currentLight);
	showDigit(secondsLeft);
	lastTickMs = millis();
}

int lastPotValue = -1;
bool potUpdated = false;

void enterConfigMode() {
	mode = MODE_CONFIG;
	configLight = LIGHT_GREEN;
	blinkPhase = true;
	lastBlinkMs = millis();
	lightOn(configLight);
	showDigit(getTimeFor(configLight));
	potUpdated = false;
	lastPotValue = potToDigit();
}

void setup() {
	// Serial.begin(9600);
	int s[] = {a, b, c, d, e, f, g};
	for (int i = 0; i < 8; i++) pinMode(s[i], OUTPUT);
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
bool buttonPressed = false;

void loop() {
	unsigned long now = millis();
	int btnRaw = digitalRead(buttonPin);
	if (btnRaw == HIGH && !buttonPressed) {
		buttonPressed = true;
		pressStart = now;
	} else if (btnRaw == LOW && buttonPressed) {
		buttonPressed = false;
		unsigned long heldTime = now - pressStart;
		// Serial.println(heldTime);
		if (heldTime >= HOLD_MS) {
			if (mode == MODE_RUN) {
				// Serial.println("Config mode");
				enterConfigMode();
			} else {
				// Serial.println("Run mode");
				enterRunMode();
			}
		} else if (mode == MODE_CONFIG) {
			int val = potToDigit();
			// Serial.print("Set seconds of led: ");
			// Serial.print(configLight);
			// Serial.print(" to ");
			// Serial.println(val);
			if (val == 0 && potUpdated) {
				beepTriple();
			} else {
				if (potUpdated) {
					setTimeFor(configLight, val);
					potUpdated = false;
				}
				beepOnce();
				configLight = nextLight(configLight);
				blinkPhase = true;
				lastBlinkMs = now;
			}
		}
	}

	if (mode == MODE_RUN) {
		now = millis();
		if (now - lastTickMs >= 1000) {
			lastTickMs = now;
			if (secondsLeft == 0) {
				currentLight = nextLight(currentLight);
				secondsLeft = getTimeFor(currentLight);
				lightOn(currentLight);
			} else {
				--secondsLeft;
			}
			showDigit(secondsLeft);
		}
	} else { // MODE_CONFIG
		if (now - lastBlinkMs >= 1000) {
			lastBlinkMs = now;
			blinkPhase = !blinkPhase;
		}
		if (blinkPhase) {
			int cand = potToDigit();
			// detect change of potentiometer
			if (!potUpdated && cand != lastPotValue) {
				potUpdated = true;
			}
			if (potUpdated) {
				showDigit(cand);
			} else {
				showDigit(getTimeFor(configLight));
			}
			lightOn(configLight);
			lastPotValue = cand;
		} else {
			clearDisplay();
			lightsOff();
		}
	}
	delay(2);
}