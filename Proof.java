import java.util.*;

public class Proof {

        private LineNumber currentLine;
        private LineNumber root;
        private TheoremSet theoremsList;

        private Stack<LineNumber> showStack = new Stack<LineNumber>();
        private LineNumber lastShow;

        private String[] reasonArray = { "print", "show", "assume", "mp", "mt",
                        "co", "ic", "repeat" };
        final private ArrayList<String> Reasons = new ArrayList<String>(
                        Arrays.asList(reasonArray));
        private ArrayList<String> proofLines = new ArrayList<String>();

        public Proof(TheoremSet theorems) {
                theoremsList = theorems;
                root = null;
                currentLine = new LineNumber("0", "default", null);
        }

        public String nextLineNumber() {
                if (currentLine.getReason().equals("show")
                                && !currentLine.getLineNumber().equals("1")) {
                        return currentLine.getLineNumber() + ".1";
                }
                if (currentLine.getLineNumber().length() == 1) {
                        int x = Integer.parseInt(currentLine.getLineNumber());
                        x++;
                        return "" + x;
                }

                Expression last;
                if (lastShow != null) {
                        last = lastShow.getExpr();
                } else {
                        last = new Expression("default");
                }

                if (currentLine.getExpr().equals(last) && currentLine.getLineNumber().length() > lastShow.getLineNumber().length()) {
                        String tobeReturned = currentLine.getLineNumber().substring(0,
                                        currentLine.getLineNumber().length() - 2);
                        int x = Integer.parseInt(tobeReturned.substring(tobeReturned
                                        .length() - 1));
                        x++;
                        tobeReturned = tobeReturned.substring(0, tobeReturned.length() - 1)
                                        + x;
                        return tobeReturned;
                } else {
                        int x = Integer.parseInt(currentLine.getLineNumber().substring(
                                        currentLine.getLineNumber().length() - 1));
                        String tobeReturned = currentLine.getLineNumber().substring(0,
                                        currentLine.getLineNumber().length() - 1);
                        x++;
                        tobeReturned = tobeReturned + x;
                        return tobeReturned;

                }

        }

        private LineNumber getLast() {
                return showStack.peek();
        }

        private static void addChild(LineNumber parent, LineNumber child) {
                if (child.getLineNumber().length() > parent.getLineNumber().length()) {
                        parent.setRightChild(child);
                } else {
                        parent.setLeftChild(child);
                }
                child.setParent(parent);
        }

        private static boolean isValidOp(char c) {
                if (c == '&' || c == '|') {
                        return true;
                }
                return false;
        }

        public static boolean isValidExpr(String expr) {
                int nested = 0;
                if (expr.length() == 1 && Character.isLowerCase(expr.charAt(0))) {
                        return true;
                } else if (expr.charAt(0) == '~') {
                        return isValidExpr(expr.substring(1));
                } else if (expr.charAt(0) == '('
                                && expr.charAt(expr.length() - 1) == ')') {
                        for (int i = 1; i < expr.length(); i++) {
                                nested += expr.charAt(i) == '(' ? 1 : 0;
                                nested -= expr.charAt(i) == ')' ? 1 : 0;
                                if (nested == 0
                                                && (expr.charAt(i) == '&' || expr.charAt(i) == '|'))
                                        return isValidExpr(expr.substring(1, i))
                                                        && isValidExpr(expr.substring(i + 1,
                                                                        expr.length() - 1));
                                if (nested == 0 && expr.charAt(i) == '='
                                                && expr.charAt(i + 1) == '>')
                                        return isValidExpr(expr.substring(1, i))
                                                        && isValidExpr(expr.substring(i + 2,
                                                                        expr.length() - 1));
                        }
                }
                return false;
        }

        public void extendProof(String x) throws IllegalLineException,
                        IllegalInferenceException {
                Map<String, Object> lineValues;
                lineValues = new HashMap<String, Object>();
                String[] Values;
                Values = x.split(" ");
                LineNumber current;
                if (nextLineNumber().length() < currentLine.getLineNumber().length()) {
                	current = lastShow;
                }else {
                	current = currentLine;
                }
                
                if (theoremsList.theorems.containsKey(Values[0])) {
                	if (Values.length != 2) {
                		throw new IllegalLineException("Invalid line: " + x);
                	}
                	if (!isEqualToTheorem(new Expression (Values[1]), (Expression) theoremsList.theorems.get(Values[0]))) {
                		throw new IllegalInferenceException("Invalid inference: theorem not applied correctly");
                	}
                	lineValues.put("reason", Values[0]);
                	lineValues.put("expr", new Expression(Values[1]));
                }

                if (nextLineNumber().equals("1") && !Values[0].equals("show")) {
                	throw new IllegalInferenceException("Invalid line: First statement should be show");
                }
                if (Values.length > 4 || Values.length < 1) {
                        throw new IllegalLineException("Invalid line format: " + x);
                }
                if (!Reasons.contains(Values[0])
                                && !theoremsList.theorems.containsKey(Values[0])) {
                        throw new IllegalLineException("Invalid reason: " + Values[0]);
                } else {
                        lineValues.put("reason", Values[0]);
                }
                
                //reason and print handler
                if (lineValues.get("reason").equals("print")) {
                        if (lineValues.size() > 1) {
                                throw new IllegalLineException("Invalid line format: " + x);
                        } else {
                                System.out.println(this.toString());
                                return;
                        }
                }

                //show and assume handler
                if (Values[0].equals("show") || Values[0].equals("assume")) {
                        if (Values.length != 2) {
                                throw new IllegalLineException("Invalid line format: "+ x);
                        }
                        if (!isValidExpr(Values[1])) { 
                                throw new IllegalLineException("Invalid expression format: " + Values[1]);
                        }
                        Expression expr = new Expression(Values[1]);
                        
                        //assume
                        if (Values[0].equals("assume")) {
                                if (!currentLine.getReason().equals("show")) {
                                        throw new IllegalInferenceException(
                                                        "Invalid assumption: Assumption must come after show statement");

                                }

                                if (!assumeChecker(expr)) {
                                        throw new IllegalInferenceException("Invalid assumption: " + expr);
                                }
                        }
                        lineValues.put("expr", expr);
                //repeat handler
                } else if (Values[0].equals("repeat")) {
                        if (Values.length != 3) {
                                throw new IllegalLineException("Invalid line format:" + x);
                        }
                        
                        //check references
                        LineNumber ref1 = isValidRef(Values[1], current);
                        if (ref1 == null) {
                                throw new IllegalLineException("Invalid reference: "
                                                + Values[1]);
                        }
                        
                        Expression expr = new Expression(Values[2]);
                        if (!ref1.getExpr().equals(expr)) {
                                throw new IllegalInferenceException(
                                                "Invalid inference. Expression, "
                                                                + expr.myRoot.fullExpr + "is not equal to "
                                                                + ref1.getExpr().myRoot.fullExpr);
                        }
                        lineValues.put("reason", Values[0]);
                        lineValues.put("expr", expr);

                //mp and mt handler
                } else if (Values[0].equals("mp") || Values[0].equals("mt")
                                || Values[0].equals("co")) {
                        
                        if (Values.length != 4) {
                                throw new IllegalLineException("Invalid line format: " + x);
                        }
                        
                        //check references
                        LineNumber ref1 = isValidRef(Values[1], current);
                        LineNumber ref2 = isValidRef(Values[2], current);
                        if (ref1 == null || ref2 == null) {
                                throw new IllegalInferenceException("Invalid line format: " + x);
                        }
                        if (!isValidExpr(Values[3])) {
                                throw new IllegalLineException("Invalid expression format: " + Values[3]);
                        }
                        
                        //make dictionary
                        lineValues.put("reason", Values[0]);
                        Expression expr = new Expression(Values[3]);
                        lineValues.put("expr", expr);

                        //mp
                        if (Values[0].equals("mp")) {
                                if ((ref2.getExpr().myRoot.myLeft == null || !ref1.getExpr().myRoot.fullExpr
                                                .equals(ref2.getExpr().myRoot.myLeft.fullExpr))
                                                && (ref1.getExpr().myRoot.myLeft == null || !(ref2.getExpr().myRoot.fullExpr)
                                                                .equals(ref1.getExpr().myRoot.myLeft.fullExpr))) {
                                        throw new IllegalInferenceException("Invalid mp inference");
                                }

                                if ((ref1.getExpr().myRoot.fullExpr.length() < ref2.getExpr().myRoot.fullExpr.length())) {
                                        if (!ref2.getExpr().myRoot.myRight.fullExpr
                                                        .equals(expr.myRoot.fullExpr)) {
                                                throw new IllegalInferenceException("Invalid mp inference");
                                        }

                                } else if (!ref1.getExpr().myRoot.myRight.fullExpr
                                                .equals(expr.myRoot.fullExpr)) {
                                        throw new IllegalInferenceException("Invalid mp reference");
                                }
                        }
                        
                        //mt
                        if (Values[0].equals("mt")) {
                                if (!mtchecker(Values[0], ref1, ref2, expr)) {
                                        throw new IllegalInferenceException(
                                                        "Invalid mt inference");
                                }
                        }

                        //co
                        if (Values[0].equals("co")) {
                                if (!cochecker(Values[0], ref1, ref2, expr)) {
                                        throw new IllegalInferenceException(
                                                        "Invalid co inference");
                                }
                        }

                //ic handler
                } else if (Values[0].equals("ic")) {
                        if (Values.length != 3) {
                                throw new IllegalLineException("Invalid line format: " + x);
                        }
                        LineNumber ref1 = isValidRef(Values[1], current);
                        if (ref1 == null) {
                                throw new IllegalInferenceException("Line " + Values[1] + " cannot be referenced");
                        }
                        if (!isValidExpr(Values[2])) {
                                System.out.println(Values[2]);
                                throw new IllegalLineException("Invalid expression format: " + Values[2]);
                        }
                        
                        //make dictionary for ic
                        lineValues.put("Ref1", ref1);
                        Expression expr = new Expression(Values[2]);// LOOK OUT HOLMES
                        lineValues.put("expr", expr);
                        
                        //check logic of ic
                        if (expr.myRoot.myRight == null
                                        || !(expr.myRoot.myRight.fullExpr).equals(isValidRef(
                                                        Values[1], current).getExpr().myRoot.fullExpr)) {
                                throw new IllegalInferenceException("Invalid ic inference");
                        }
                        if (!(this.getLast().getExpr().myRoot.fullExpr
                                        .equals(expr.myRoot.fullExpr))) {
                                throw new IllegalInferenceException("Invalid ic inference");
                        }
                }

                String lineNumber = nextLineNumber();
                LineNumber newLine = new LineNumber(lineNumber,
                                (String) (lineValues.get("reason")),
                                (Expression) lineValues.get("expr"));
                LineNumber parent;
                if (newLine.getLineNumber().equals("1")) {
                        root = newLine;
                } else {
                        if (newLine.getLineNumber().length() < currentLine.getLineNumber()
                                        .length()) {
                                parent = lastShow;

                        } else {
                                parent = currentLine;
                        }
                        addChild(parent, newLine);
                }

                if (!showStack.empty() && newLine.getExpr().equals(getLast().getExpr())) {
                        lastShow = showStack.pop();
                }

                if (Values[0].equals("show")) {
                        showStack.push(newLine);
                }

                currentLine = newLine;
                proofLines.add(currentLine.getLineNumber() + "    " + x);
        }
        
        public static boolean isEqualToTheorem(Expression app, Expression theorem) {
    		ArrayDeque<ExpressionNode> appQ = new ArrayDeque<ExpressionNode>();
    		ArrayDeque<ExpressionNode> theoremQ = new ArrayDeque<ExpressionNode>();
    		HashMap<Integer, String> HashitUp = new HashMap<Integer, String>();
    		if (app.myRoot.fullExpr.length() < theorem.myRoot.fullExpr.length()) {

    			return false;
    		}

    		return isEqualHelp(app.myRoot, theorem.myRoot, appQ, theoremQ, HashitUp);
    	}

    	private static boolean isEqualHelp(ExpressionNode app,
    			ExpressionNode theorem, ArrayDeque<ExpressionNode> appQ,
    			ArrayDeque<ExpressionNode> theoremQ,
    			HashMap<Integer, String> HashitUp) {
    		Integer key = 0;
    		String value = "";

    		if (!app.myItem.equals(theorem.myItem) && !(theorem.myLeft == null)
    				&& !(theorem.myRight == null)) { // recursive?

    			return false;
    		}
    		if (theorem.myLeft == null && theorem.myRight == null) { // are you a leaf?
    																	

    			key = theorem.hashCode();

    			if (app.fullExpr != null) {
    				value = app.fullExpr;

    			}
    			if (HashitUp.containsKey(key)) {

    				if (!HashitUp.get(key).equals(value)) {

    					return false;
    				} else if (appQ.size() != 0 && theoremQ.size() != 0) {
    					return isEqualHelp(appQ.pop(), theoremQ.pop(), appQ,
    							theoremQ, HashitUp);
    				} else {
    					return true;
    				}

    			} else {

    				HashitUp.put(key, value);

    				if (appQ.size() != 0 && theoremQ.size() != 0) {
    					return isEqualHelp(appQ.pop(), theoremQ.pop(), appQ,
    							theoremQ, HashitUp);
    				} else {
    					return true;
    				}
    			}
    		}
    		if (theorem.myLeft != null) {

    			theoremQ.add(theorem.myLeft);

    		}
    		if (theorem.myRight != null) {

    			theoremQ.add(theorem.myRight);
    		}
    		if (app.myLeft != null) {

    			appQ.add(app.myLeft);

    		}
    		if (app.myRight != null) {

    			appQ.add(app.myRight);
    		}
    		if (appQ.size() != theoremQ.size()) { // Is queue same size? Same number children
    												

    			return false;
    		}

    		if (appQ.size() != 0) {

    			if (theoremQ.size() != 0) {
    				if (appQ.size() != 0 && theoremQ.size() != 0) {
    					return isEqualHelp(appQ.pop(), theoremQ.pop(), appQ,
    							theoremQ, HashitUp);
    				} else {
    					return true;
    				}
    			}
    		}

    		return true;
    	}

        public boolean mtchecker(String reason, LineNumber ref1, LineNumber ref2,
                        Expression expr) {
                // find ref1
                LineNumber notRef;
                LineNumber inferenceRef;
                if (ref1.getExpr().myRoot.myItem.equals("~")) {
                        notRef = ref1;
                        if (ref2.getExpr().myRoot.myItem.equals("=>")) {
                                inferenceRef = ref2;
                        } else {
                                return false;
                        }
                } else if (ref2.getExpr().myRoot.myItem.equals("~")) {
                        notRef = ref2;
                        if (ref1.getExpr().myRoot.myItem.equals("=>")) {
                                inferenceRef = ref1;
                        } else {
                                return false;
                        }
                } else {
                        return false;
                }

                if (!notRef.getExpr().myRoot.myLeft.fullExpr.equals(inferenceRef
                                .getExpr().myRoot.myRight.fullExpr)) {
                        return false;
                }
                if (!expr.myRoot.myItem.equals("~") || !inferenceRef.getExpr().myRoot.myLeft.fullExpr
                                .equals(expr.myRoot.myLeft.fullExpr)) {
                        return false;
                }
                return true;
        }

        public boolean cochecker(String reason, LineNumber ref1, LineNumber ref2,
                        Expression expr) {
                if (ref1.getExpr().myRoot.myItem.equals("~")) {
                        if (!ref2.getExpr().myRoot.fullExpr
                                        .equals(ref1.getExpr().myRoot.myLeft.fullExpr)) {
                                return false;
                        }
                } else if (ref2.getExpr().myRoot.myItem.equals("~")) {
                        if (!ref1.getExpr().myRoot.fullExpr
                                        .equals(ref2.getExpr().myRoot.myLeft.fullExpr)) {
                                return false;
                        }
                } else
                        return false;

                return true;
        }

        private boolean assumeChecker(Expression expr) {
                if (expr.myRoot.myLeft != null
                                && currentLine.getExpr().myRoot.fullExpr
                                                .equals(expr.myRoot.myLeft.fullExpr)) {
                        if (expr.myRoot.myItem.equals("~")) {
                                return true;
                        }
                }
                if (currentLine.getExpr().myRoot.myItem.equals("=>")) {
                        if (currentLine.getExpr().myRoot.myLeft.fullExpr
                                        .equals(expr.myRoot.fullExpr)) {
                                return true;
                        }
                }
                return false;
        }

        private LineNumber isValidRef(String reference, LineNumber current) {
                LineNumber ref =  isValidRefHelper(reference, current);
                if (showStack.search(ref) == -1){
                        return ref;
                } else {
                        return null;
                }
                
        }

        private static LineNumber isValidRefHelper(String reference,
                        LineNumber current) {
                if (current.getLineNumber().equals(reference)) {
                        return current;
                }
                if (current.getParent() == null) {
                        return null;
                } else {
                        return isValidRefHelper(reference, current.getParent());
                }
        }

        public String toString() {
                String tobeReturned = "";
                for (int i = 0; i < proofLines.size(); i++) {
                        tobeReturned += proofLines.get(i) + "\n";
                }
                return tobeReturned;
        }

        public boolean isComplete() {
                if (currentLine.getLineNumber().equals("1")) {
                        return false;
                }
                return showStack.empty();
        }

        public static void main(String[] args) throws IllegalLineException,
                        IllegalInferenceException {
                Proof a = new Proof(new TheoremSet());
                String s = "show (((p=>q)=>q)=>((q=>p)=>p))";
                // 1
                a.extendProof(s);
                // 2
                a.extendProof("assume ((p=>q)=>q)");
                // 3
                a.extendProof("show ((q=>p)=>p)");
                // 3.1
                a.extendProof("assume (q=>p)");
                // 3.2
                a.extendProof("show p");
                // 3.2.1
                a.extendProof("assume ~p");
                System.out.println(a.mtchecker("mt", a.currentLine, a.currentLine
                                .getParent().getParent(), new Expression("~q")));
                a.print();

        }

        public void print() {
                if (root != null) {

                        printHelper(root, 0);
                }
        }

        private static final String indent1 = "    ";

        private static void printHelper(LineNumber root, int indent) {
                if (root != null) {
                        printHelper(root.getLeftChild(), indent + 1);
                        println(root, indent);
                        printHelper(root.getRightChild(), indent + 1);
                }
        }

        private static void println(LineNumber num, int indent) {
                for (int k = 0; k < indent; k++) {
                        System.out.print(indent1);
                }
                System.out.println(num.getLineNumber() + ", " + num.getReason() + ", "
                                + num.getExpr());
        }
}