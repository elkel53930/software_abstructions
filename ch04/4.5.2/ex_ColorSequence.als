abstract sig Color {}
one sig Red, Yellow, Green extends Color {}
fun colorSequence: Color -> Color {
	Color <: iden + Red -> Green + Green-> Yellow + Yellow -> Red
	}

run {}
