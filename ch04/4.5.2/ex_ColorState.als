abstract sig Color {}
one sig Red, Yellow, Green extends Color{}

sig Light {}
sig LightState {color: Light -> one Color}
sig Junction {lights: set Light}

fun redLights (s: LightState): set Light {s.color.Red}
pred mostlyRed (s: LightState, j: Junction) {
	lone j.lights - redLights [s]
	}


run {}
