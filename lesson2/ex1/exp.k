require "modules/substitution.k"
module EXP-SYNTAX

syntax Exp ::= Int
						| Exp "*" Exp 				[seqstrict]
						| Exp "/" Exp 				[seqstrict]
						> Exp "+" Exp 				[seqstrict]
						| Exp "-" Exp 				[seqstrict]
						| "read"
						| "print" "("	Exp ")"	[strict]
						| "(" Exp ")"  				[bracket]
						| "let" Id "=" Exp "in" Exp [strict(2)]

						syntax KResult ::= Int

syntax Ids ::= List{Id, ","}

syntax Stmt ::= Exp ";" [strict]
            | "var" Ids ";"
            | Id "=" Exp ";" [strict(2)]
            | Stmt Stmt [left]

endmodule

module EXP
	imports EXP-SYNTAX
	imports SUBSTITUTION

	configuration
	<T>
		<k> $PGM:K </k> <streams >
    <env> .Map </env>
    <store> .Map </store>
		<in stream="stdin"> .List </in>
		<out stream="stdout"> .List </out> </streams>
	</T>

	rule V:KResult ; => .K

	rule I1:Int + I2:Int => I1 +Int I2

	rule I1:Int - I2:Int => I1 -Int I2

	rule I1:Int * I2:Int => I1 *Int I2

	rule I1:Int / I2:Int => I1 /Int I2 requires I2 =/=Int 0

	rule <k> print(I:Int) => I:Int ... </k>
	     <out> ... .List => ListItem(I) </out>

	rule <k> read => I:Int ... </k>
			 <in> ListItem(I) => .List ... </in>

	rule let X:Id = I:Int in E:Exp => E[I/X]

	rule St1:Stmt St2:Stmt => St1 ~> St2

  	rule <k> var (X:Id, X1:Ids => X1) ; ... </k>
    	<env> Rho:Map => Rho[X <- !N:Int] </env>
    	<store> ... .Map => !N |-> 0  </store>
    		requires notBool(X in keys(Rho))

	rule <k> X:Id => I:Int ... </k>
       <env> ... X |-> L:Int ... </env>
       <store> ... L |-> I:Int ... </store>

	rule <k> X:Id = I:Int; => I; ... </k>
       <env> ... X |-> L:Int ... </env>
       <store > ... L |-> (_ => I) ... </store>

	rule var .Ids ; => .K [structural]

endmodule
