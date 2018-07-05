/*
sig Peer{
	friends: set Peer,
	community: set this.*@friends
	}
*/

sig Peer {
	friends,
	community: set Peer
	}
fact {
	community in *friends}

run {} for 5
