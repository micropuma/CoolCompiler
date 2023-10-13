-- check for inheritance cycle and other inheritance errors
Class A inherits B {

};

Class B inherits C {

};

Class C inherits D {

};

Class D inherits B {

};
