class C {
	a : Int;
	b : Bool;

	init(x : Int, y : Bool) : C {
           {
		a <- x;
		b <- y;
		self;
           }
	};

    return_bool(x: Int, y: Bool, z: Bool) : Bool {
        return false;
    };
};

class D {

}

Class Main {
	main():C {
	  (new C).init(1,true)
	};
};