public class LineNumber {
	private String linenum;
	private String reason;
	private Expression expr;
	private String fullLine;
	private LineNumber parent;
	private LineNumber leftChild;
	private LineNumber rightChild;
	
	public LineNumber(String linenum, String reason, Expression expr) {
		this.linenum = linenum;
		this.reason = reason;
		this.expr = expr;
	}
	
	public String getLineNumber ( ) {
		return linenum;
	}
	
	public String getReason(){
		return reason;
	}
	
	public LineNumber getParent() {
		return parent;
	}
	
	public void setParent(LineNumber parent) {
		this.parent = parent;
	}

	public Expression getExpr() {
		return expr;
	}
	
	public LineNumber getLeftChild() {
		return leftChild;
	}
	
	public LineNumber getRightChild() {
		return rightChild;
	}
	
	public void setLeftChild(LineNumber child) {
		leftChild = child;
	}
	
	public void setRightChild(LineNumber child) {
		rightChild = child;
	}
}
