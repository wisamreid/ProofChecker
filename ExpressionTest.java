import junit.framework.TestCase;


public class ExpressionTest extends TestCase {
	
	public void testExpressionTrees1() throws IllegalLineException {
		Expression expr = new Expression("(((k&m)|b)=>(k&m))");
		assertEquals(expr.myRoot.myItem, "=>");
		assertEquals(expr.myRoot.myLeft.myItem, "|");
		assertEquals(expr.myRoot.myRight.myItem, "&");
		assertEquals(expr.myRoot.myLeft.myLeft.myItem, "&");
		assertEquals(expr.myRoot.myLeft.myRight.myItem, "b");
		assertEquals(expr.myRoot.myRight.myLeft.myItem, "k");
		assertEquals(expr.myRoot.myRight.myRight.myItem, "m");
		assertEquals(expr.myRoot.myLeft.myLeft.myLeft.myItem, "k");
		assertEquals(expr.myRoot.myLeft.myLeft.myRight.myItem, "m");

	}

	public void testExpressionTrees2() throws IllegalLineException {
		Expression expr = new Expression("~~(p&q)");
		assertEquals(expr.myRoot.myItem, "~");
		assertEquals(expr.myRoot.myLeft.myItem, "~");
		assertEquals(expr.myRoot.myLeft.myLeft.myItem, "&");
		assertEquals(expr.myRoot.myLeft.myLeft.myLeft.myItem, "p");
		assertEquals(expr.myRoot.myLeft.myLeft.myRight.myItem, "q");
		assertEquals(expr.myRoot.myLeft.myLeft.myRight.myLeft, null);
		assertEquals(expr.myRoot.myLeft.myLeft.myRight.myRight, null);
	}
	
}
