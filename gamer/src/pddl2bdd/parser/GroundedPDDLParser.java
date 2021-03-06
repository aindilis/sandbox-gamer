/* Generated By:JavaCC: Do not edit this line. GroundedPDDLParser.java */
package pddl2bdd.parser;
import pddl2bdd.parser.logic.*;
import java.io.*;
import java.util.*;

public class GroundedPDDLParser implements GroundedPDDLParserConstants {
    public static void parse(String partitionFileName)
    {
        String domainFileName = partitionFileName.substring(0, partitionFileName.length() - 8) + "Dom.gdl";
        String problemFileName = partitionFileName.substring(0, partitionFileName.length() - 8) + "Prob.gdl";
        if (partitionFileName.startsWith("abstract"))
        {
            String [] partitionFileNameParts = partitionFileName.split("-", 2);
            partitionFileName = "orig-" + partitionFileNameParts [1];
        }
        System.out.println("prob: " + problemFileName);
        System.out.println("dom: " + domainFileName);
        System.out.println("part: " + partitionFileName);
        try
        {
            FileInputStream fis;
            GroundedPDDLParser parser;
            actions = new Vector < Action > ();
            initialState = new Vector < Predicate > ();
            partitioning = new Vector < Vector < Predicate > > ();
            File goalBDDFile = new File("goal");
            if (!goalBDDFile.exists())
            {
                System.out.println("Parsing domain file...");
                fis = new FileInputStream(domainFileName);
                parser = new GroundedPDDLParser(fis);
                lastCost = 0;
                parser.domain();
                System.out.println("done.");
                System.out.println("Parsing problem file...");
                fis = new FileInputStream(problemFileName);
                parser.ReInit(fis);
                parser.problem();
                System.out.println("done.");
                System.out.println("Parsing partition file...");
                fis = new FileInputStream(partitionFileName);
                parser.ReInit(fis);
                    parser.partition();
                    System.out.println("done.");
                    System.out.println("Checking for only del-effects from groups with no \'none-of-these\'-variables...");
                LinkedList<LinkedList<String>> partition = new LinkedList<LinkedList<String>>();
                ListIterator<Vector<Predicate>> partitionIt = partitioning.listIterator();
                        while (partitionIt.hasNext()) {
                            Vector<Predicate> group = partitionIt.next();
                            ListIterator<Predicate> groupIt = group.listIterator();
                            LinkedList<String> singlePartition = new LinkedList<String>();
                            while (groupIt.hasNext()) {
                                singlePartition.add(groupIt.next().getName());
                            }
                            partition.add(singlePartition);
                        }
                ListIterator < Action > actionIt = actions.listIterator();
                boolean errorFound = false;
                while (actionIt.hasNext())
                {
                        errorFound |= actionIt.next().checkEffect(partition);
                }
                if (errorFound) {
                        StringBuilder output = new StringBuilder(10000);
                        ListIterator<LinkedList<String>> partitionStringIt = partition.listIterator();
                        while (partitionStringIt.hasNext()) {
                                LinkedList<String> part = partitionStringIt.next();
                                ListIterator<String> partIt = part.listIterator();
                                output.append("[]\n");
                                while (partIt.hasNext()) {
                                    output.append("(" + partIt.next() + ")\n");
                                }
                                output.append("[]\n");
                        }
                            FileWriter writer;
                            try {
                                writer = new FileWriter(partitionFileName);
                                writer.write(output.toString());
                                writer.close();
                                System.out.println("Parsing partition file again...");
                                partitioning.clear();
                                fis = new FileInputStream(partitionFileName);
                                parser.ReInit(fis);
                                    parser.partition();
                                    System.out.println("done.");
                            } catch (Exception e) {
                                System.err.println(e.getMessage());
                                System.exit(1);
                            }
                }
                System.out.println("done.");
            }
            else
            {
                System.out.println("Parsing partition file...");
                fis = new FileInputStream(partitionFileName);
                parser = new GroundedPDDLParser(fis);
                    parser.partition();
                    System.out.println("done.");
            }
        }
        catch (Exception e)
        {
            System.err.println("Error: " + e.getMessage());
            System.exit(1);
        }
    }

    public static boolean isUniformCost()
    {
        if (actions.size() == 0) // should only happen if goalBDD file is present, so that a PDB has been generated
        {
            return false;
        }
        ListIterator < Action > actionIt = actions.listIterator();
        int lastFoundCost = - 1;
        while (actionIt.hasNext())
        {
            int cost = actionIt.next().getCost();
            if (lastFoundCost == - 1)
            {
                lastFoundCost = cost;
            }
            else
            {
                if (lastFoundCost != cost)
                {
                    return false;
                }
            }
        }
        // if no costs present or all uniform, set costs to 1, in case of A* search
        actionIt = actions.listIterator();
        while (actionIt.hasNext())
        {
            actionIt.next().setCost(1);
        }
        return true;
    }

    public static void cleanup()
    {
        actions.clear();
        actions = null;
        initialState.clear();
        initialState = null;
        goalDescription = null;
        partitioning.clear();
        partitioning = null;
    }

    public static Vector < Action > actions;

    public static Vector < Predicate > initialState;

    public static Expression goalDescription;

    public static Vector < Vector < Predicate > > partitioning;

    public static int lastCost;

  static final public void domain() throws ParseException {
    jj_consume_token(DEFINE_TOK);
    domainDeclaration();
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case REQUIRE_TOK:
      requirements();
      break;
    default:
      jj_la1[0] = jj_gen;
      ;
    }
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case PREDS_TOK:
      predicates();
      break;
    default:
      jj_la1[1] = jj_gen;
      ;
    }
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case FUNC_TOK:
      functions();
      break;
    default:
      jj_la1[2] = jj_gen;
      ;
    }
    label_1:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case ACTION_TOK:
        ;
        break;
      default:
        jj_la1[3] = jj_gen;
        break label_1;
      }
      action();
    }
    jj_consume_token(25);
  }

  static final public void domainDeclaration() throws ParseException {
    jj_consume_token(DOMAIN_TOK);
    jj_consume_token(NAME);
    jj_consume_token(25);
  }

  static final public void requirements() throws ParseException {
    jj_consume_token(REQUIRE_TOK);
    label_2:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case 26:
        ;
        break;
      default:
        jj_la1[4] = jj_gen;
        break label_2;
      }
      jj_consume_token(26);
      jj_consume_token(NAME);
    }
    jj_consume_token(25);
  }

  static final public void predicates() throws ParseException {
    jj_consume_token(PREDS_TOK);
    label_3:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case 27:
        ;
        break;
      default:
        jj_la1[5] = jj_gen;
        break label_3;
      }
      predicate();
    }
    jj_consume_token(25);
  }

  static final public void functions() throws ParseException {
    jj_consume_token(FUNC_TOK);
    label_4:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case 27:
        ;
        break;
      default:
        jj_la1[6] = jj_gen;
        break label_4;
      }
      predicate();
    }
    jj_consume_token(25);
  }

  static final public void action() throws ParseException {
    Action action;
    Token name;
    Expression prec;
    Expression eff;
    jj_consume_token(ACTION_TOK);
    name = jj_consume_token(NAME);
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case PARAM_TOK:
      parameters();
      break;
    default:
      jj_la1[7] = jj_gen;
      ;
    }
    prec = precondition();
    eff = effect();
    jj_consume_token(25);
        action = new Action();
        action.setName(name.image);
        action.setPrecondition(prec);
        action.setEffect(eff);
        action.setCost(lastCost);
        actions.add(action);
        lastCost = 0;
  }

  static final public void parameters() throws ParseException {
    jj_consume_token(PARAM_TOK);
    jj_consume_token(27);
    jj_consume_token(25);
  }

  static final public Expression precondition() throws ParseException {
    Expression expr;
    jj_consume_token(PREC_TOK);
    expr = expression();
        {if (true) return expr;}
    throw new Error("Missing return statement in function");
  }

  static final public Expression effect() throws ParseException {
    Expression expr;
    jj_consume_token(EFF_TOK);
    expr = effExpression();
        {if (true) return expr;}
    throw new Error("Missing return statement in function");
  }

  static final public Expression expression() throws ParseException {
    Expression expr;
    Vector < Expression > exprList;
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case 27:
      expr = predicate();
        {if (true) return expr;}
      break;
    case OR_TOK:
      jj_consume_token(OR_TOK);
        exprList = new Vector < Expression > ();
      label_5:
      while (true) {
        switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
        case OR_TOK:
        case AND_TOK:
        case NOT_TOK:
        case 27:
          ;
          break;
        default:
          jj_la1[8] = jj_gen;
          break label_5;
        }
        expr = expression();
            exprList.add(expr);
      }
      jj_consume_token(25);
        expr = new AndOrTerm();
        ((AndOrTerm) expr).setIsAndTerm(false);
        ((AndOrTerm) expr).setTerms(exprList);
        {if (true) return expr;}
      break;
    case AND_TOK:
      jj_consume_token(AND_TOK);
        exprList = new Vector < Expression > ();
      label_6:
      while (true) {
        switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
        case OR_TOK:
        case AND_TOK:
        case NOT_TOK:
        case 27:
          ;
          break;
        default:
          jj_la1[9] = jj_gen;
          break label_6;
        }
        expr = expression();
            exprList.add(expr);
      }
      jj_consume_token(25);
        expr = new AndOrTerm();
        ((AndOrTerm) expr).setIsAndTerm(true);
        ((AndOrTerm) expr).setTerms(exprList);
        {if (true) return expr;}
      break;
    case NOT_TOK:
      jj_consume_token(NOT_TOK);
      expr = expression();
      jj_consume_token(25);
        NotTerm ret = new NotTerm();
        ret.setTerm(expr);
        {if (true) return ret;}
      break;
    default:
      jj_la1[10] = jj_gen;
      jj_consume_token(-1);
      throw new ParseException();
    }
    throw new Error("Missing return statement in function");
  }

  static final public Expression effExpression() throws ParseException {
    Expression condpre;
    Expression expr;
    Vector < Expression > exprList;
    Token cost;
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case 27:
      expr = predicate();
        {if (true) return expr;}
      break;
    case AND_TOK:
      jj_consume_token(AND_TOK);
        exprList = new Vector < Expression > ();
      label_7:
      while (true) {
        switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
        case AND_TOK:
        case NOT_TOK:
        case INC_TOK:
        case WHEN_TOK:
        case 27:
          ;
          break;
        default:
          jj_la1[11] = jj_gen;
          break label_7;
        }
        expr = effExpression();
            if (expr != null)
            {
                exprList.add(expr);
            }
      }
      jj_consume_token(25);
        expr = new AndOrTerm();
        ((AndOrTerm) expr).setIsAndTerm(true);
        ((AndOrTerm) expr).setTerms(exprList);
        {if (true) return expr;}
      break;
    case NOT_TOK:
      jj_consume_token(NOT_TOK);
      expr = effExpression();
      jj_consume_token(25);
        if (expr == null)
        {
            System.err.println("Error: Cannot handle action costs in negation!");
            System.exit(1);
        }
        NotTerm ret = new NotTerm();
        ret.setTerm(expr);
        {if (true) return ret;}
      break;
    case INC_TOK:
      jj_consume_token(INC_TOK);
      predicate();
      cost = jj_consume_token(NUMBER);
      jj_consume_token(25);
        if (lastCost > 0)
        {
            System.err.println("Error: At least two action costs provided!");
            System.exit(1);
        }
        lastCost = Integer.parseInt(cost.image);
        {if (true) return null;}
      break;
    case WHEN_TOK:
      jj_consume_token(WHEN_TOK);
      condpre = expression();
      expr = condeffExpression();
      jj_consume_token(25);
        if (condpre == null)
        {
            System.err.println("Error in parsing conditional effect's condition!");
            System.exit(1);
        }
        if (expr == null)
        {
            System.err.println("Error in parsing conditional effect's effect!");
            System.exit(1);
        }
        Condition cond = new Condition();
        cond.setPre(condpre);
        cond.setEff(expr);
        {if (true) return cond;}
      break;
    default:
      jj_la1[12] = jj_gen;
      jj_consume_token(-1);
      throw new ParseException();
    }
    throw new Error("Missing return statement in function");
  }

  static final public Expression condeffExpression() throws ParseException {
    Expression expr;
    Vector < Expression > exprList;
    Token cost;
    switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
    case 27:
      expr = predicate();
        {if (true) return expr;}
      break;
    case AND_TOK:
      jj_consume_token(AND_TOK);
        exprList = new Vector < Expression > ();
      label_8:
      while (true) {
        switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
        case AND_TOK:
        case NOT_TOK:
        case INC_TOK:
        case 27:
          ;
          break;
        default:
          jj_la1[13] = jj_gen;
          break label_8;
        }
        expr = condeffExpression();
            if (expr != null)
            {
                exprList.add(expr);
            }
      }
      jj_consume_token(25);
        expr = new AndOrTerm();
        ((AndOrTerm) expr).setIsAndTerm(true);
        ((AndOrTerm) expr).setTerms(exprList);
        {if (true) return expr;}
      break;
    case NOT_TOK:
      jj_consume_token(NOT_TOK);
      expr = condeffExpression();
      jj_consume_token(25);
        if (expr == null)
        {
            System.err.println("Error: Cannot handle action costs in negation!");
            System.exit(1);
        }
        NotTerm ret = new NotTerm();
        ret.setTerm(expr);
        {if (true) return ret;}
      break;
    case INC_TOK:
      jj_consume_token(INC_TOK);
      predicate();
      cost = jj_consume_token(NUMBER);
      jj_consume_token(25);
        System.err.println("Error: Action costs in conditional effects not supported!");
        System.exit(1);
      break;
    default:
      jj_la1[14] = jj_gen;
      jj_consume_token(-1);
      throw new ParseException();
    }
    throw new Error("Missing return statement in function");
  }

  static final public Predicate predicate() throws ParseException {
    Token name;
    jj_consume_token(27);
    name = jj_consume_token(NAME);
    jj_consume_token(25);
        Predicate pred = new Predicate();
        pred.setName(name.image);
        {if (true) return pred;}
    throw new Error("Missing return statement in function");
  }

  static final public void problem() throws ParseException {
    jj_consume_token(DEFINE_TOK);
    problemDeclaration();
    domainTest();
    init();
    goal();
    jj_consume_token(25);
  }

  static final public void problemDeclaration() throws ParseException {
    jj_consume_token(PROBLEM_TOK);
    jj_consume_token(NAME);
    jj_consume_token(25);
  }

  static final public void domainTest() throws ParseException {
    jj_consume_token(DOMAIN_TEST_TOK);
    jj_consume_token(NAME);
    jj_consume_token(25);
  }

  static final public void init() throws ParseException {
    Predicate pred;
    jj_consume_token(INIT_TOK);
    label_9:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case 27:
        ;
        break;
      default:
        jj_la1[15] = jj_gen;
        break label_9;
      }
      pred = predicate();
            initialState.add(pred);
    }
    jj_consume_token(25);
  }

  static final public void goal() throws ParseException {
    Expression expr;
    jj_consume_token(GOAL_TOK);
    expr = expression();
    jj_consume_token(25);
        goalDescription = expr;
  }

  static final public void partition() throws ParseException {
    label_10:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case 28:
        ;
        break;
      default:
        jj_la1[16] = jj_gen;
        break label_10;
      }
      group();
    }
  }

  static final public void group() throws ParseException {
    Predicate pred;
    Vector < Predicate > group;
    jj_consume_token(28);
    jj_consume_token(29);
        group = new Vector < Predicate > ();
    label_11:
    while (true) {
      switch ((jj_ntk==-1)?jj_ntk():jj_ntk) {
      case 27:
        ;
        break;
      default:
        jj_la1[17] = jj_gen;
        break label_11;
      }
      pred = predicate();
            group.add(pred);
    }
    jj_consume_token(28);
    jj_consume_token(29);
        partitioning.add(group);
  }

  static private boolean jj_initialized_once = false;
  /** Generated Token Manager. */
  static public GroundedPDDLParserTokenManager token_source;
  static SimpleCharStream jj_input_stream;
  /** Current token. */
  static public Token token;
  /** Next token. */
  static public Token jj_nt;
  static private int jj_ntk;
  static private int jj_gen;
  static final private int[] jj_la1 = new int[18];
  static private int[] jj_la1_0;
  static {
      jj_la1_init_0();
   }
   private static void jj_la1_init_0() {
      jj_la1_0 = new int[] {0x80,0x100,0x200,0x400,0x4000000,0x8000000,0x8000000,0x800,0x801c000,0x801c000,0x801c000,0x8078000,0x8078000,0x8038000,0x8038000,0x8000000,0x10000000,0x8000000,};
   }

  /** Constructor with InputStream. */
  public GroundedPDDLParser(java.io.InputStream stream) {
     this(stream, null);
  }
  /** Constructor with InputStream and supplied encoding */
  public GroundedPDDLParser(java.io.InputStream stream, String encoding) {
    if (jj_initialized_once) {
      System.out.println("ERROR: Second call to constructor of static parser.  ");
      System.out.println("       You must either use ReInit() or set the JavaCC option STATIC to false");
      System.out.println("       during parser generation.");
      throw new Error();
    }
    jj_initialized_once = true;
    try { jj_input_stream = new SimpleCharStream(stream, encoding, 1, 1); } catch(java.io.UnsupportedEncodingException e) { throw new RuntimeException(e); }
    token_source = new GroundedPDDLParserTokenManager(jj_input_stream);
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 18; i++) jj_la1[i] = -1;
  }

  /** Reinitialise. */
  static public void ReInit(java.io.InputStream stream) {
     ReInit(stream, null);
  }
  /** Reinitialise. */
  static public void ReInit(java.io.InputStream stream, String encoding) {
    try { jj_input_stream.ReInit(stream, encoding, 1, 1); } catch(java.io.UnsupportedEncodingException e) { throw new RuntimeException(e); }
    token_source.ReInit(jj_input_stream);
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 18; i++) jj_la1[i] = -1;
  }

  /** Constructor. */
  public GroundedPDDLParser(java.io.Reader stream) {
    if (jj_initialized_once) {
      System.out.println("ERROR: Second call to constructor of static parser. ");
      System.out.println("       You must either use ReInit() or set the JavaCC option STATIC to false");
      System.out.println("       during parser generation.");
      throw new Error();
    }
    jj_initialized_once = true;
    jj_input_stream = new SimpleCharStream(stream, 1, 1);
    token_source = new GroundedPDDLParserTokenManager(jj_input_stream);
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 18; i++) jj_la1[i] = -1;
  }

  /** Reinitialise. */
  static public void ReInit(java.io.Reader stream) {
    jj_input_stream.ReInit(stream, 1, 1);
    token_source.ReInit(jj_input_stream);
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 18; i++) jj_la1[i] = -1;
  }

  /** Constructor with generated Token Manager. */
  public GroundedPDDLParser(GroundedPDDLParserTokenManager tm) {
    if (jj_initialized_once) {
      System.out.println("ERROR: Second call to constructor of static parser. ");
      System.out.println("       You must either use ReInit() or set the JavaCC option STATIC to false");
      System.out.println("       during parser generation.");
      throw new Error();
    }
    jj_initialized_once = true;
    token_source = tm;
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 18; i++) jj_la1[i] = -1;
  }

  /** Reinitialise. */
  public void ReInit(GroundedPDDLParserTokenManager tm) {
    token_source = tm;
    token = new Token();
    jj_ntk = -1;
    jj_gen = 0;
    for (int i = 0; i < 18; i++) jj_la1[i] = -1;
  }

  static private Token jj_consume_token(int kind) throws ParseException {
    Token oldToken;
    if ((oldToken = token).next != null) token = token.next;
    else token = token.next = token_source.getNextToken();
    jj_ntk = -1;
    if (token.kind == kind) {
      jj_gen++;
      return token;
    }
    token = oldToken;
    jj_kind = kind;
    throw generateParseException();
  }


/** Get the next Token. */
  static final public Token getNextToken() {
    if (token.next != null) token = token.next;
    else token = token.next = token_source.getNextToken();
    jj_ntk = -1;
    jj_gen++;
    return token;
  }

/** Get the specific Token. */
  static final public Token getToken(int index) {
    Token t = token;
    for (int i = 0; i < index; i++) {
      if (t.next != null) t = t.next;
      else t = t.next = token_source.getNextToken();
    }
    return t;
  }

  static private int jj_ntk() {
    if ((jj_nt=token.next) == null)
      return (jj_ntk = (token.next=token_source.getNextToken()).kind);
    else
      return (jj_ntk = jj_nt.kind);
  }

  static private java.util.List jj_expentries = new java.util.ArrayList();
  static private int[] jj_expentry;
  static private int jj_kind = -1;

  /** Generate ParseException. */
  static public ParseException generateParseException() {
    jj_expentries.clear();
    boolean[] la1tokens = new boolean[30];
    if (jj_kind >= 0) {
      la1tokens[jj_kind] = true;
      jj_kind = -1;
    }
    for (int i = 0; i < 18; i++) {
      if (jj_la1[i] == jj_gen) {
        for (int j = 0; j < 32; j++) {
          if ((jj_la1_0[i] & (1<<j)) != 0) {
            la1tokens[j] = true;
          }
        }
      }
    }
    for (int i = 0; i < 30; i++) {
      if (la1tokens[i]) {
        jj_expentry = new int[1];
        jj_expentry[0] = i;
        jj_expentries.add(jj_expentry);
      }
    }
    int[][] exptokseq = new int[jj_expentries.size()][];
    for (int i = 0; i < jj_expentries.size(); i++) {
      exptokseq[i] = (int[])jj_expentries.get(i);
    }
    return new ParseException(token, exptokseq, tokenImage);
  }

  /** Enable tracing. */
  static final public void enable_tracing() {
  }

  /** Disable tracing. */
  static final public void disable_tracing() {
  }

}
