Hello world should work:

  $ aslref hello_world.asl
  Hello, world!

ASL Typing Reference:
  $ aslref TypingRule.TypeSatisfaction1.asl
  $ aslref TypingRule.TypeSatisfaction2.asl
  $ aslref TypingRule.TypeSatisfaction3.asl
  File TypingRule.TypeSatisfaction3.asl, line 14, characters 2 to 6:
  ASL Typing error: a subtype of pairT was expected,
    provided (integer {1}, T2).
  [1]
  $ aslref TypingRule.Block0.asl
  3
  Some text
//  $ aslref TypingRule.EConcatUnresolvableToInteger.asl
  $ aslref TypingRule.ApplyBinopTypes.asl
  $ aslref TypingRule.LDDiscard.asl
  $ aslref TypingRule.LDVar.asl
  $ aslref TypingRule.LDTyped.asl
  $ aslref TypingRule.LDTuple.asl
  $ aslref TypingRule.Lit.asl

ASL Typing Reference / annotating types:
  $ aslref TypingRule.TReal.asl
  $ aslref TypingRule.TBool.asl
  $ aslref TypingRule.TNamed.asl
  $ aslref TypingRule.TIntUnConstrained.asl
  $ aslref TypingRule.TIntWellConstrained.asl
  $ aslref TypingRule.TIntUnderConstrained.asl
  $ aslref TypingRule.TBits.asl
  $ aslref TypingRule.TTuple.asl
  $ aslref TypingRule.TArray.asl
  $ aslref --no-exec TypingRule.TEnumDecl.asl
  $ aslref TypingRule.TRecordExceptionDecl.asl
  $ aslref TypingRule.TNonDecl.asl
  File TypingRule.TNonDecl.asl, line 1, characters 5 to 6:
  ASL Error: Cannot parse.
  [1]
  $ aslref TypingRule.TBitField.asl
  $ aslref --no-exec TypingRule.AnnotateFuncSig.asl
  $ aslref TypingRule.BuiltinAggregateTypes.asl
  $ aslref --no-exec TypingRule.BuiltinExceptionType.asl
  $ aslref TypingRule.BuiltinSingularTypes.asl
  $ aslref TypingRule.EnumerationType.asl
  $ aslref TypingRule.TString.asl
  $ aslref TypingRule.ConstraintMod.bad.asl
  File TypingRule.ConstraintMod.bad.asl, line 9, characters 4 to 5:
  ASL Typing error: a subtype of integer {0..2} was expected,
    provided integer {3}.
  [1]
