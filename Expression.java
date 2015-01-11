import java.util.*;

public class Expression {
        ExpressionNode myRoot;
        
        public Expression (String s) {
                myRoot = exprTree(s);           
        }


        public static ExpressionNode exprTree(String expr) {
            if (expr.charAt (0) != '(') {
                if (expr.charAt(0) == '~'){
                        return new ExpressionNode(expr, "~", exprTree(expr.substring(1)), null);
                }
                return new ExpressionNode(expr, expr,null,null); 
            } else {
                // expr is a parenthesized expression.
                // Strip off the beginning and ending parentheses,
                // find the main operator (an occurrence of + or * not nested
                // in parentheses, and construct the two subtrees.
           
                int nesting = 0;
                int opPos = 0;
                int opLength = 0;
                for (int k=1; k<expr.length()-1; k++) {
                    if (expr.charAt(k) == '('){
                        nesting++;
                    } else if(expr.charAt(k) == ')'){
                        nesting--;
                    } else if(nesting == 0) {
                        if((expr.charAt(k) == '|') || (expr.charAt(k) == '&')){         
                                opPos = k;
                                opLength = 1;
                        } else if((nesting == 0) && (expr.substring(k, k+2).equals("=>"))){
                                opPos = k;
                                opLength = 2;
                        }
                    }
                }
                
                String opnd1 = expr.substring (1, opPos);
                String opnd2 = expr.substring (opPos+opLength, expr.length()-1);
                String op = expr.substring (opPos, opPos+opLength);
                //System.out.println ("expression = " + expr);
                //System.out.println ("operand 1  = " + opnd1);
                //System.out.println ("operator   = " + op);
                //System.out.println ("operand 2  = " + opnd2);
                //System.out.println ( );
                return new ExpressionNode(expr, op, exprTree(opnd1), exprTree(opnd2)); 
            }
        }
        
        
        
        public void print ( ) {
            if (myRoot != null) {
                printHelper (myRoot, 0);
            }
        }
                
        private static final String indent1 = "    ";
                
        private static void printHelper (ExpressionNode root, int indent) {
                if (root.myRight != null){
                    printHelper(root.myRight, indent + 1);
                }
            println (root.myItem, indent);
                if (root.myLeft != null){
                    printHelper(root.myLeft, indent+ 1);
                }
        }
                        
        private static void println (Object obj, int indent) {
            for (int k=0; k<indent; k++) {
                System.out.print (indent1);
            }
            System.out.println (obj);
        }
        
        public boolean equals(Expression e) {
        	return this.myRoot.fullExpr.equals(e.myRoot.fullExpr);
        }
        
        
}



class ExpressionNode {
        String myItem, fullExpr;
        ExpressionNode myLeft, myRight;
        public ExpressionNode(String fullExpr, String myItem, ExpressionNode myLeft, ExpressionNode myRight){
                this.myItem = myItem;
                this.myLeft = myLeft;
                this.myRight = myRight;
                this.fullExpr = fullExpr;
        }
        
        public int hashCode(){
        	return this.fullExpr.hashCode();
        	
        }
}