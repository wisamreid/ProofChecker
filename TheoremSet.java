import java.util.HashMap;

public class TheoremSet {
	public HashMap<String,Object> theorems;
	public TheoremSet ( ) {
		theorems = new HashMap<String,Object>();
	}

	public Expression put (String s, Expression e) {
		theorems.put(s, e);
		return e;
	}
}
