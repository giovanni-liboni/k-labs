// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "k-equal.k"
require "int.k"


module SET
  imports INT-SYNTAX-HOOKS
  imports K-TECHNIQUE

  /*@ \section{Description} The Set represents a mathematical set (a collection
   of unique items). */

  /*@ Construct a new Set as the union of two different sets ($A \cup B$) */
  syntax Set ::= Set Set                  [left, function, hook(Set:__), klabel('_Set_)]
  /*@ Construct an empty Set */
  syntax Set ::= ".Set"                   [function, hook(Set:.Set)]
               //| "."
  /*@ Construct a singleton Set (a Set with only one element $\{ a \}$). To add
   an element $a$ to a set $A$, construct the union of the singleton set
   $\{ a \}$ and $A$ ($\{ a \} \cup A$). */
  syntax Set ::= SetItem(K)               [function, hook(Set:SetItem)]

  /*@ Get the intersection of two sets ($A \cap B$) */
  syntax Set ::= intersectSet(Set, Set)   [function, hook(Set:intersection)]

  /*@ Get the difference of two sets ($A \setminus B$)*/
  syntax Set ::= Set "-Set" Set           [function, hook(Set:difference), latex({#1}-_{\it Set}{#2})]

  /*@ Check element membership in a set ($a \in A$) */
  syntax Bool ::= K "in" Set              [function, hook(Set:in)]

  /*@ Check set inclusion ($A \subseteq B$) */
  syntax Bool ::= Set "<=Set" Set         [function, hook(Set:inclusion)]

  /*@ Get the cardinality of a set ($|A|$) */
  syntax Int ::= size(Set)                [function, hook(Collection:size)]

  /*@ Get an arbitrarily chosen element of the Set */
  syntax K ::= choice(Set)                [function, hook(Set:choice), klabel(Set:choice)]

  /* set difference axioms */
  // TODO(AndreiS): remove this if not used
  //rule S1:Set -Set (SetItem(K:K) S2:Set) => S1 -Set S2
  //when notBool(K in S1)
  //rule S:Set -Set .Set => S
endmodule

