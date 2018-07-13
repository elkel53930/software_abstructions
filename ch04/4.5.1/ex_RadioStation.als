sig RadioStation {band: set Freq}
sig Freq {}
fact NoOverlapping {
	no disj s,s': RadioStation | some s.band & s'.band
	}

run {}
