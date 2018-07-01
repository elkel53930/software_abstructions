// 色の定義
enum Color{Red, Yellow, Green}

// 正しい色の順番を示す関係、を返す関数
fun ccolorSequence: Color -> Color{
	Color <: iden + Red -> Green + Green -> Yellow + Yellow -> Red
}

// 信号機の集合
sig Light{}

// 信号機の状態
sig LightState {color: Light -> one Color}

// 合流点
sig Junction{lights: set Light}
