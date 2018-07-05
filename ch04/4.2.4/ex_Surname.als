sig Name {}
sig Person {surname: Name, parents: set Person}
	{surname in parents.surname}
