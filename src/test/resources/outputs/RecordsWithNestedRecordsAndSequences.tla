---- MODULE RecordsWithNestedRecordsAndSequences -----

EXTENDS TLC, Sequences

CONSTANTS
          n1,
          n2,
          n3
Foo2 ==
        [
          action |-> {
                       <<
                          <<
                             1,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             2,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 1))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             2,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 1))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             3,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 2))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             3,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 2))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             4,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 3))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             4,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 3))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             5,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             5,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             6,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             6,
                             [
                               counter |-> (n1 :> (n1 :> 0 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             7,
                             [
                               counter |-> (n1 :> (n1 :> 1 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             7,
                             [
                               counter |-> (n1 :> (n1 :> 1 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             8,
                             [
                               counter |-> (n1 :> (n1 :> 2 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             8,
                             [
                               counter |-> (n1 :> (n1 :> 2 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             9,
                             [
                               counter |-> (n1 :> (n1 :> 3 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             9,
                             [
                               counter |-> (n1 :> (n1 :> 3 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             10,
                             [
                               counter |-> (n1 :> (n1 :> 4 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>
                       >>,
                       <<
                          <<
                             10,
                             [
                               counter |-> (n1 :> (n1 :> 4 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>,
                          [
                            name |-> "S!Next",
                            location |-> [
                                           beginLine |-> 46,
                                           beginColumn |-> 1,
                                           endLine |-> 46,
                                           endColumn |-> 18,
                                           module |-> "MCCRDT"
                                         ]
                          ],
                          <<
                             10,
                             [
                               counter |-> (n1 :> (n1 :> 4 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                             ]
                          >>
                       >>
                     },
          state |-> {
                      <<
                         1,
                         [
                           counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0))
                         ]
                      >>,
                      <<
                         2,
                         [
                           counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 1))
                         ]
                      >>,
                      <<
                         3,
                         [
                           counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 2))
                         ]
                      >>,
                      <<
                         4,
                         [
                           counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 3))
                         ]
                      >>,
                      <<
                         5,
                         [
                           counter |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                         ]
                      >>,
                      <<
                         6,
                         [
                           counter |-> (n1 :> (n1 :> 0 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                         ]
                      >>,
                      <<
                         7,
                         [
                           counter |-> (n1 :> (n1 :> 1 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                         ]
                      >>,
                      <<
                         8,
                         [
                           counter |-> (n1 :> (n1 :> 2 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                         ]
                      >>,
                      <<
                         9,
                         [
                           counter |-> (n1 :> (n1 :> 3 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                         ]
                      >>,
                      <<
                         10,
                         [
                           counter |-> (n1 :> (n1 :> 4 @@ n2 :> 4) @@ n2 :> (n1 :> 0 @@ n2 :> 4))
                         ]
                      >>
                    }
        ]

=====
