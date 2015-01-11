import junit.framework.TestCase;


public class ProofTest extends TestCase {
	
	//testProof1 is our basic proof and tests that a simple case can be completed.
	public void testProof1() throws IllegalLineException, IllegalInferenceException{
		Proof p = new Proof(new TheoremSet());
		p.extendProof("show (q=>q)");
		p.extendProof("assume q");
		p.extendProof("ic 2 (q=>q)");
		assertTrue(p.isComplete());
	}

	//testProof2 tests going in and out of subproofs correctly using nextLineNumber()
	public void testProof2() throws IllegalLineException, IllegalInferenceException{
		Proof p = new Proof(new TheoremSet());
		p.extendProof("show (p=>(~p=>q))");
		p.extendProof("assume p");
		p.extendProof("show (~p=>q)");
		assertEquals("3.1", p.nextLineNumber()); //goes into subproof correctly
		p.extendProof("assume ~p");
		p.extendProof("co 2 3.1 (~p=>q)");
		assertEquals("4", p.nextLineNumber());  //exits subproof correctly
		p.extendProof("ic 3 (p=>(~p=>q))");
		assertTrue(p.isComplete());
	}
	
	//testProof3 tests exiting multiple subproofs in a row. We initially had an issue with this because the most recent
	//"show" statement had not been popped off before nextLineNumber was called, so this tests it specifically.
	//This also tests "mt" and "co".
	public void testProof3() throws IllegalLineException, IllegalInferenceException{
		Proof p = new Proof(new TheoremSet());
		p.extendProof("show (((p=>q)=>q)=>((q=>p)=>p))");
		p.extendProof("assume ((p=>q)=>q)");
		p.extendProof("show ((q=>p)=>p)");
		p.extendProof("assume (q=>p)");
		p.extendProof("show p");
		p.extendProof("assume ~p");
		p.extendProof("mt 3.2.1 3.1 ~q");
		p.extendProof("mt 2 3.2.2 ~(p=>q)");
		p.extendProof("show (p=>q)");
		p.extendProof("assume p");
		p.extendProof("co 3.2.4.1 3.2.1 (p=>q)");
		//testing exiting multiple subproofs in a row
		assertEquals("3.2.5", p.nextLineNumber());
		p.extendProof("co 3.2.4 3.2.3 p");
		assertEquals("3.3", p.nextLineNumber());
		p.extendProof("ic 3.2 ((q=>p)=>p)");
		assertEquals("4", p.nextLineNumber());
		p.extendProof("ic 3 (((p=>q)=>q)=>((q=>p)=>p))");
		assertTrue(p.isComplete());
		}
	
	//This tests the repeat function. It also tests if you try to finish a subproof but it throws an exception, the "show"
	//statement does not get popped off prematurely. This tests "ic" as well.
	public void testRepeat() throws IllegalLineException, IllegalInferenceException{
		Proof p = new Proof(new TheoremSet());
		p.extendProof("show (p=>p)");
		p.extendProof("show (p=>p)");
		p.extendProof("assume p");
		try {
			p.extendProof("ic 2 (p=>p)");
			assertTrue(false);
		} catch (Exception e){
			assertTrue(e instanceof IllegalInferenceException);
		}
		p.extendProof("ic 2.1 (p=>p)");
		assertEquals("3", p.nextLineNumber());
		p.extendProof("repeat 2 (p=>p)");
		assertTrue(p.isComplete());		
	}
	
	//This tests "mp" specifically and more "ic" statements.
	public void testSampleProof6() throws IllegalLineException, IllegalInferenceException{
		Proof p = new Proof(new TheoremSet());
		p.extendProof("show ((a=>(b=>c))=>((a=>b)=>(a=>c)))"); //1
		p.extendProof("assume (a=>(b=>c))"); //2
		assertEquals("3", p.nextLineNumber()); 
		p.extendProof("show ((a=>b)=>(a=>c))"); //3
 		p.extendProof("assume (a=>b)"); //3.1
		p.extendProof("show (a=>c)"); //3.2
		p.extendProof("assume a"); //3.2.1
		p.extendProof("mp 2 3.2.1 (b=>c)"); //3.2.2
		p.extendProof("mp 3.2.1 3.1 b"); //3.2.3
		assertEquals("3.2.4", p.nextLineNumber());
		p.extendProof("mp 3.2.3 3.2.2 c"); //3.2.4
		p.extendProof("ic 3.2.4 (a=>c)"); //3.2.5
		p.extendProof("ic 3.2 ((a=>b)=>(a=>c))"); //3.3
		p.extendProof("ic 3 ((a=>(b=>c))=>((a=>b)=>(a=>c)))"); // 4
		assertTrue(p.isComplete());	
	}
	
	//This proof tests the use of theorems and tries to catch a mixture of different errors
	public void testTheorems() throws IllegalLineException, IllegalInferenceException{
		TheoremSet s = new TheoremSet();
		s.put("not-or-creation", new Expression("(~p=>(~q=>~(p|q)))"));
		Proof p = new Proof(s);
		assertEquals("1", p.nextLineNumber());
		p.extendProof("show ((a=>q)=>((b=>q)=>((a|b)=>q)))");
		try {
			p.extendProof("assume a=>q"); //Tests line format (lacks parens)
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalLineException);
		}
		assertEquals("2", p.nextLineNumber());
		p.extendProof("assume (a=>q)");
		assertEquals("3", p.nextLineNumber());
		p.extendProof("show ((b=>q)=>((a|b)=>q))");
		try {
			p.extendProof("assume b"); //Tests assume (have to assume whole left side of inference)
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		assertEquals("3.1", p.nextLineNumber());
		p.extendProof("assume (b=>q)");
		assertEquals("3.2", p.nextLineNumber());
		p.extendProof("show ((a|b)=>q)");
		try {
			p.extendProof("assume (a&b)"); //Tests assume (have to assume whole left side of inference)
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		try {
			p.extendProof("assume q"); //Tests assume (have to assume whole left side of inference)
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		assertEquals("3.2.1", p.nextLineNumber());
		p.extendProof("assume (a|b)");
		assertEquals("3.2.2", p.nextLineNumber());
		p.extendProof("show q");
		try {
			p.extendProof("assume (~q)"); //Tests line format (unnecessary parens)
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalLineException);
		}
		assertEquals("3.2.2.1", p.nextLineNumber());
		p.extendProof("assume ~q");
		try {
			p.extendProof("mt 2.2.2.1 2 a"); //bad line number (line number doesn't exist)
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		try {
			p.extendProof("mt 3.2.1 2 a"); //bad inference (should be ~a)
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		try {
			p.extendProof("mt 3.2.2.1 2 a"); //bad inference (wrong line number)
			assertTrue(false);
		} catch (Exception e) {
			System.out.println(e);
			assertTrue(e instanceof IllegalInferenceException);
		}
		assertEquals("3.2.2.2", p.nextLineNumber());
		p.extendProof("mt 3.2.2.1 2 ~a");
		assertEquals("3.2.2.3", p.nextLineNumber());
		p.extendProof("mt 3.1 3.2.2.1 ~b");
		try {
			p.extendProof("not-o-creation (~a=>(~b=>~(a|b)))"); //Tests theorem usage: theorem name is spelled wrong
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalLineException);
		}
		try {
			p.extendProof("not-or-creation (~a=>(~b=>~(b|b)))"); //bad theorem application: p is a theorem variable
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		assertEquals("3.2.2.4", p.nextLineNumber());
		p.extendProof("not-or-creation (~a=>(~b=>~(a|b)))");
		p.extendProof("mp 3.2.2.4 3.2.2.2 (~b=>~(a|b))");
		try {
			p.extendProof("mq 3.2.2.3 3.2.2.5 ~(a|b)"); //since reason isn't mp, mt, co, or ic, it must be a theorem name but it does not exist
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalLineException);
		}
		p.extendProof("mp 3.2.2.3 3.2.2.5 ~(a|b)");
		p.extendProof("co 3.2.2.6 3.2.1 ((a=>q)=>((b=>q)=>((a|b)=>q)))");
		p.extendProof("co 3.2.2.6 3.2.1 q");
		try {
			p.extendProof("ic 3.2.2.8 ((a|b)=>q)"); //cannot access this reference line
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		p.extendProof("ic 3.2.2 ((a|b)=>q)");
		p.extendProof("ic 3.2 ((b=>q)=>((a|b)=>q))");
		p.extendProof("ic 3 ((a=>q)=>((b=>q)=>((a|b)=>q)))");
		assertTrue(p.isComplete());
		
	}
	
	//testSampleProof3 tests multiple tildes and makes sure that it does not affect the flow of the proof.
	public void testSampleProof3() throws IllegalLineException, IllegalInferenceException {
		Proof p = new Proof(new TheoremSet());
		p.extendProof("show (~~p=>p)");
		p.extendProof("assume ~~p");
		assertEquals("3", p.nextLineNumber());
		p.extendProof("show p");
		p.extendProof("assume ~p");
		assertEquals("3.2", p.nextLineNumber());
		p.extendProof("co 2 3.1 p");
		p.extendProof("ic 3 (~~p=>p)");
		assertTrue(p.isComplete());
	}
	
	//testSampleProof1 tests that the first line of a proof has to be a "show" statement. It also tests random garbage statements that
	//users could mistakenly put in that should not break the code. It also tests that you cannot put an assume statement after a non-
	//show statement.
	public void testSampleProof1() throws IllegalLineException, IllegalInferenceException {
		Proof p = new Proof(new TheoremSet());
		try {
			p.extendProof("assume p");
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		p.extendProof("show ((a=>b)=>((b=>c)=>(a=>c)))");
		p.extendProof("assume (a=>b)");
		p.extendProof("show ((b=>c)=>(a=>c))");
		try {
			p.extendProof("aasdfjas;dlf"); //inserting garbage
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalLineException);
		}
		p.extendProof("assume (b=>c)");
		p.extendProof("show (a=>c)");
		p.extendProof("assume a");
		p.extendProof("show c");
		p.extendProof("assume ~c");
		p.extendProof("mt 3.2.2.1 3.1 ~b");
		p.extendProof("mt 2 3.2.2.2 ~a");
		try {
			p.extendProof("assume ~c"); //testing putting assume after a non-show statement
			assertTrue(false);
		}catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		try {
			p.extendProof("co 3.2.2.3 3.2.1");
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalLineException);
		}
		p.extendProof("co 3.2.2.3 3.2.1 c");
		try {
			p.extendProof("ic 3.2.2.4 (a=>c)");
			assertTrue(false);
		} catch (Exception e) {
			assertTrue(e instanceof IllegalInferenceException);
		}
		p.extendProof("ic 3.2.2 (a=>c)");
		p.extendProof("ic 3.2 ((b=>c)=>(a=>c))");
		p.extendProof("ic 3 ((a=>b)=>((b=>c)=>(a=>c)))");
		assertTrue(p.isComplete());
	}
	
		// testing a valid application of a theorem with nested expressions
		public void testTheoremChecker1() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(((a|b)=>c)=>(a|b))");
			Expression theorem = new Expression("((a=>c)=>a)");
			assertTrue(Proof.isEqualToTheorem(app, theorem));
		}

		// testing an invalid application of a theorem with nested expressions
		public void testTheoremChecker2() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(((a|b)&(b|c))=>(c|b))");
			Expression theorem = new Expression("((a&b)=>a)");
			assertFalse(Proof.isEqualToTheorem(app, theorem));
		}

		// testing an application with less complexity than the theorem
		public void testTheoremChecker3() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("((a=>c)=>a)");
			Expression theorem = new Expression("(((a|b)=>c)=>(a|b))");
			assertFalse(Proof.isEqualToTheorem(app, theorem));
		}

		// testing mismatched operators in application
		public void testTheoremChecker4() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(((a&b)=>c)=>(a|b))");
			Expression theorem = new Expression("((a=>c)=>a)");
			assertFalse(Proof.isEqualToTheorem(app, theorem));
		}

		// testing mismatched operators between the application and the theorem
		public void testTheoremChecker5() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(((a|b)=>c)=>(a|b))");
			Expression theorem = new Expression("((a&c)=>a)");
			assertFalse(Proof.isEqualToTheorem(app, theorem));
		}

		// testing trivial edge case
		public void testTheoremChecker6() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("c");
			Expression theorem = new Expression("a");
			assertTrue(Proof.isEqualToTheorem(app, theorem));
		}

		// testing trivial expressions
		public void testTheoremChecker7() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(a=>b)");
			Expression theorem = new Expression("(b=>c)");
			assertTrue(Proof.isEqualToTheorem(app, theorem));
		}

		// testing top level operator mismatch
		public void testTheoremChecker8() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(a=>b)");
			Expression theorem = new Expression("(a&c)");
			assertFalse(Proof.isEqualToTheorem(app, theorem));
		}

		// testing expressions with a not operator
		public void testTheoremChecker9() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(((a|b)=>c)=>~(a|b))");
			Expression theorem = new Expression("((a=>c)=>~a)");
			assertTrue(Proof.isEqualToTheorem(app, theorem));
		}

		// testing expressions with double not operators
		public void testTheoremChecker10() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(~~(a|b)=>(a|b))");
			Expression theorem = new Expression("(~~a=>a)");
			assertTrue(Proof.isEqualToTheorem(app, theorem));
		}

		// testing expressions with double not operators
		public void testTheoremChecker11() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(~~~(a|b)=>~(a|b))");
			Expression theorem = new Expression("(~~~a=>~a)");
			assertTrue(Proof.isEqualToTheorem(app, theorem));
		}

		// testing invalid application of not operators
		public void testTheoremChecker12() throws IllegalLineException,
				IllegalInferenceException {
			Expression app = new Expression("(~~(a|b)=>~(a|b))");
			Expression theorem = new Expression("(~~a=>a)");
			assertFalse(Proof.isEqualToTheorem(app, theorem));
		}
		
		public void testIsValidExpr1(){
            String s = "()";
            assertFalse(Proof.isValidExpr(s));//empty expression
            
    }
    public void testIsValidExpr2(){
            String s = "p";
            assertTrue(Proof.isValidExpr(s));//single element expression
            
    }
    public void testIsValidExpr3(){
            String s = "(p=>q)";
            assertTrue(Proof.isValidExpr(s));//basic 2 element expression with on operator
    }
    public void testIsValidExpr4(){
            String s = "(r|s)";
            assertTrue(Proof.isValidExpr(s));
    }
    public void testIsValidExpr5(){
            String s = "((p&q)=>p)";//nested expression, 2 operators
            assertTrue(Proof.isValidExpr(s));
    }
    public void testIsValidExpr6(){
            String s = "(((p=>q)=>q)=>((q=>p)=>p))";//nested expressions on both sides of main operator
            assertTrue(Proof.isValidExpr(s));
    }
    public void testIsValidExpr7(){
            String s = "(()=>";
            assertFalse(Proof.isValidExpr(s));// illegal number of parenthesis, operator on outside, no expression variables
    }
    public void testIsValidExpr8(){
            String s ="(())=>";
            assertFalse(Proof.isValidExpr(s));//legal number of parethesis, operator on outside, no expression variables
    }
    public void testisValidExpr9(){
            String s = "(~~~p=>q|(p&q))";
            assertFalse(Proof.isValidExpr(s));// does not match legal number of parenthesis per operator
    }
    public void testIsValidExpr10(){
            String s = "(~~~p=>(q|(p&q)))";
            assertTrue(Proof.isValidExpr(s));//upper parenthesis mistake corrected, also tests multiple "~"(nots)
    }
    public void testIsValidExpr11(){
            String s = "((~~~p=>q)|(p&(q|zt)))";//correct number of operators, one extra expression variable in nested expr: "zt"
            assertFalse(Proof.isValidExpr(s));
    }
    


}
