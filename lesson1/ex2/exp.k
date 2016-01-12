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
endmodule

module EXP
	imports EXP-SYNTAX
	imports SUBSTITUTION

	configuration
	<T>
		<k> $PGM:K </k> <streams >
		<in stream="stdin"> .List </in>
		<out stream="stdout"> .List </out> </streams>
	</T>

	rule I1:Int + I2:Int => I1 +Int I2

	rule I1:Int - I2:Int => I1 -Int I2

	rule I1:Int * I2:Int => I1 *Int I2

	rule I1:Int / I2:Int => I1 /Int I2 requires I2 =/=Int 0

	rule <k> print(I:Int) => I:Int ... </k>
	     <out> ... .List => ListItem(I) </out>

	rule <k> read => I:Int ... </k>
			 <in> ListItem(I) => .List ... </in>

	rule let X:Id = I:Int in E:Exp => E[I/X]

endmodule
