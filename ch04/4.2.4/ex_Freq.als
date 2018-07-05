sig RadioStation {class: StationClass, freq: Freq}
	{freq in class.band}
sig StationClass {band: set Freq}
sig Freq{}

run {}
