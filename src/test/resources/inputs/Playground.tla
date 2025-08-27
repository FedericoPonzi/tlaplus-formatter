---------------------- MODULE Playground ----------------------
EXTENDS Naturals, TLC
CONSTANTS a,b, counter, n1, n2
Foo ==
    [ action |->
        { << << 1,
                    [ counter |->
                        ( n1 :> ( n1 :> 0 @@ n2 :> 0 ) @@
                            n2 :>
                                ( n1 :> 0 @@
                                        n2 :>
                                            0
                                        )
                            )
                        ]
                    >>,

==============================================================
