
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Arrays;
import java.util.ArrayList;

public class Tableaux {

    
    
    Expression rootFormula;
    Branch start;
    LinkedList<Branch> branches;

    LinkedList<Branch> unfinishedBranches;


    public Tableaux() {
        branches = new LinkedList<>();
        unfinishedBranches = new LinkedList<>();
    }

    public void doTableaux(Expression startExpression) {
        rootFormula = startExpression;
        start = new Branch(new TableauxPart(startExpression, null, null, null), null);
        unfinishedBranches.add(start);

        while (!unfinishedBranches.isEmpty()) {
            Branch current = unfinishedBranches.getFirst();

            LinkedList<Branch> result = current.nextStep();
            

            if (result == null) {
                
                branches.add(current);
                
                unfinishedBranches.remove(current);
                
            } else {
                for (int i = 0; i < result.size(); i++) {
                    if (!unfinishedBranches.contains(result.get(i))) {
                        unfinishedBranches.add(result.get(i));
                    }
                }
            }
        }
        
    }

    

    public String toString() {
        String s = "\n";
        for (int i = 0; i < branches.size(); i++) {
            s += "Branch nr: " + i;
            s += branches.get(i).toString();
            s += "\n";
        }
        return s;
    }

}

class Branch {

    List<TableauxRules> destructivList = Arrays.asList(
        TableauxRules.AND,
        TableauxRules.NOT,
        TableauxRules.NOTSATIS,
        TableauxRules.NOTNOT,
        TableauxRules.SATIS,
        TableauxRules.NOTAND,
        TableauxRules.E,
        TableauxRules.DIAMOND
    );

    private static final boolean AddLoopCheck = false;
    private static final int Showlines = 0;

    

    public LinkedList<TableauxPart> tableauxParts;
    LinkedList<TableauxPart> upNext;
    TableauxPart currentStep;
    Branch from;

    
 
    HashMap<Expression, LinkedList<TableauxRules>> exprRulesApplied;
    LinkedList<String> nomsInBranch;

    
    

    boolean EndBranch = true;

    boolean notEInEffect = false;
    LinkedList<TableauxPart> origNotEParts;

    boolean notDiamondInEffect = false;
    LinkedList<TableauxPart> origNotDiamondParts;


    public Branch(TableauxPart startTab, Branch from) {

        this.tableauxParts = new LinkedList<>();
        this.tableauxParts.add(startTab);
        this.currentStep = startTab;
        this.upNext = new LinkedList<>();
        upNext.add(startTab);

        this.from = from;

        if (this.from == null) {
            exprRulesApplied = new HashMap<Expression, LinkedList<TableauxRules>>() {
            };
            nomsInBranch = new LinkedList<>();
            origNotEParts = new LinkedList<>();
            origNotDiamondParts = new LinkedList<>();
        } else {
            exprRulesApplied = this.from.exprRulesApplied;
            nomsInBranch = this.from.nomsInBranch;
            origNotEParts = this.from.origNotEParts;
            origNotDiamondParts = this.from.origNotDiamondParts;
        }
    }

    //|||   Focuse  |||
    

    public String addNotToString(TableauxPart part){
        String StringPart = part.expr.toString();
        String minusPart = "";
        if (StringPart.charAt(0)!='-'){
            if ((StringPart.length()==3)||(StringPart.charAt(0)!='(')){
                minusPart = "-("+StringPart+")";
            } else {minusPart = "-"+StringPart;}
        }
        if (StringPart.charAt(0)=='-'){
            if (StringPart.length()!=3){
                minusPart = "-("+StringPart+")";
            } else {minusPart = "-"+StringPart;}
            minusPart = StringPart.substring(2, StringPart.length()-1);
            
        }
        return minusPart;
    
    }
    
    public void addSATISFIER(TableauxPart part){

        if (this.from != null){
            part.contradiction = (this.from.currentStep.contradiction);

        }
        
        TableauxPart PreviouseStep = part;
        String NotPart = addNotToString(part);
        while (PreviouseStep != null) {
            
            PreviouseStep = PreviouseStep.from;
            if((PreviouseStep != null) && NotPart.equals(PreviouseStep.expr.toString())){
                part.contradiction = (true);
            }
        }
    
    }


    //|||   Focuse  |||

    public void addToBranch(TableauxPart part, boolean upNext) {
        if (currentStep.seekExpressionInBranch(part.expr)&!AddLoopCheck) {
            return;
        }
        if (exprRulesApplied.get(part.expr) != null){
            if(exprRulesApplied.get(part.expr).contains(part.ruleApplied) && destructivList.contains(part.ruleApplied)&!AddLoopCheck) {

                    
                    return;
                    
            }
        }
        if (currentStep.lineNumber <= Showlines){
            System.out.println(currentStep);
        }
        
        documentRule(tableauxParts.getFirst().expr, part.ruleApplied);
        

        
        this.currentStep = part;
        this.tableauxParts.add(part);
        
        if (upNext) {
            this.upNext.add(part);
        }
        
    }

    public void documentRule(Expression ex, TableauxRules ruleApplied) {
        if (exprRulesApplied.get(ex) == null) {
            exprRulesApplied.put(ex, new LinkedList<>());
        }
        exprRulesApplied.get(ex).add(ruleApplied);
    }

    public void applyAnd(Expression parent, Expression left, Expression right, TableauxPart current,
        LinkedList<Branch> returnBranches, TableauxRules ruleApplied) {
        TableauxPart andLeft = new TableauxPart(left, this.currentStep, current, ruleApplied);
        addToBranch(andLeft, true);
        addSATISFIER(andLeft);
        TableauxPart andRight = new TableauxPart(right, this.currentStep, current, ruleApplied);
        
        addToBranch(andRight, true);

        addSATISFIER(andRight);
        returnBranches.add(this);
        
        
    }

    public void applyOr(Expression parent, Expression left, Expression right, TableauxPart current,
            LinkedList<Branch> returnBranches, TableauxRules ruleApplied) {
        documentRule(parent, ruleApplied);
        EndBranch = false;
        TableauxPart orLeft = new TableauxPart(left, this.currentStep, current, ruleApplied,
                this.currentStep.lineNumber + 1);
        TableauxPart orRight = new TableauxPart(right, this.currentStep, current, ruleApplied,
                this.currentStep.lineNumber + 2);
        returnBranches.add(this);
        
        returnBranches.add(new Branch(orLeft, this));
        addSATISFIER(orLeft);
        returnBranches.add(new Branch(orRight, this));
        addSATISFIER(orRight);
        
    }

    public void applyNotE(TableauxPart origNotEPart, Nominal nominal) {
        Expression origNotEExpr = null;
        try {
            origNotEExpr = ((E) ((Satisfier) ((Not) origNotEPart.expr).proposition).proposition).proposition;
        } catch (Exception e) {
            System.err.println(e.getMessage());
            return;
        }
        TableauxPart newNotE = new TableauxPart(new Not(new Satisfier(nominal, origNotEExpr)), this.currentStep,
                origNotEPart, TableauxRules.NOTE);
        addToBranch(newNotE, false);
        upNext.add(newNotE);
        addSATISFIER(newNotE);
    }

    public void applyNotDiamond(TableauxPart origNotDiamondPart) {
        Diamond notSatisDiamond = (Diamond) ((Satisfier) ((Not) origNotDiamondPart.expr).proposition).proposition;
        Nominal desiredNominal = ((Satisfier) ((Not) origNotDiamondPart.expr).proposition).referencePoint;
        Nominal result = this.currentStep.seekNotDiamondRule(desiredNominal.identifier);
        if (result != null) {
            TableauxPart notSatisOldNominal = new TableauxPart(
                    new Not(new Satisfier(result, notSatisDiamond.proposition)), this.currentStep, origNotDiamondPart,
                    TableauxRules.NOTDIAMOND);
            addToBranch(notSatisOldNominal, true);
            addSATISFIER(notSatisOldNominal);
        }
    }

    public void newNominal(String id, TableauxPart from, TableauxPart source) {
        nomsInBranch.add(id);
        TableauxPart ref = new TableauxPart(new Satisfier(new Nominal(id), new Nominal(id)), from, source,
                TableauxRules.REF);
        addToBranch(ref, false);
        addSATISFIER(ref);
        if (notEInEffect) {
            for (int i = 0; i < origNotEParts.size(); i++) {
                applyNotE(origNotEParts.get(i), new Nominal(id));
                addSATISFIER(origNotEParts.get(i));
            }
        }
        if (notDiamondInEffect) {
            for (int i = 0; i < origNotDiamondParts.size(); i++) {
                applyNotDiamond(origNotDiamondParts.get(i));
                addSATISFIER(origNotDiamondParts.get(i));
            }
        }
    }

    public void applyNomRule(TableauxPart target, String targetId) {
        LinkedList<Satisfier> foundNomRelations = this.currentStep.seekAllNominalRelations(targetId, null);
        LinkedList<Satisfier> foundNomRuleFormula = this.currentStep.seekAllNomRuleFormula(targetId, null);

        if (foundNomRelations.size() > 0 && foundNomRuleFormula.size() > 0) {
            for (int i = 0; i < foundNomRelations.size(); i++) {
                String oldNom = foundNomRelations.get(i).referencePoint.identifier;
                String newNom = ((Nominal) foundNomRelations.get(i).proposition).identifier;

                if (oldNom == newNom) {
                    continue;
                }

                for (int j = 0; j < foundNomRuleFormula.size(); j++) {
                    Expression innerPart = foundNomRuleFormula.get(j).proposition;
                    TableauxRules rule = innerPart.getType() == ExpressionTypes.DIAMOND ? TableauxRules.NOM2
                            : TableauxRules.NOM1;
                    TableauxPart newRelation = new TableauxPart(new Satisfier(new Nominal(newNom), innerPart),
                            this.currentStep, target, rule);

                    boolean expressionInBranch = this.currentStep.seekExpressionInBranch(newRelation.expr);
                    if (expressionInBranch) {
                        continue;
                    }
                    addToBranch(newRelation, true);
                    addSATISFIER(newRelation);
                }

            }
        }
        
    }

    public LinkedList<Branch> nextStep() {

        LinkedList<Branch> returnBranches = new LinkedList<>();

        if (upNext.isEmpty()) {
            return null;
        }

        TableauxPart current = upNext.getFirst();
        upNext.removeFirst();

        Expression expr = current.expr;
        ExpressionTypes type = expr.getType();

        //exprRulesApplied.put(s, new LinkedList<>());

        for (String nominalId : nomsInBranch) {
            applyNomRule(current, nominalId);
        }

        switch (type) {
            case AND:
                And and = (And) expr;
                applyAnd(expr, and.propositionLeft, and.propositionRight, current, returnBranches, TableauxRules.AND);
                
                break;
            case OR:
                Or or = (Or) expr;
                applyOr(expr, or.propositionLeft, or.propositionRight, current, returnBranches, TableauxRules.OR);
                break;
            case SATISFIER:
                Expression satisProp = ((Satisfier) expr).proposition;
                Nominal satisNominal = (Nominal) ((Satisfier) expr).referencePoint;
                if (!nomsInBranch.contains(satisNominal.identifier)) {
                    newNominal(satisNominal.identifier, current, current);
                }
                switch (satisProp.getType()) {
                    case NOT:
                        Not statisNot = (Not) satisProp;
                        TableauxPart notSatis = new TableauxPart(
                                new Not(new Satisfier(satisNominal, statisNot.proposition)), this.currentStep, current,
                                TableauxRules.NOT);
                        addToBranch(notSatis, true);
                        returnBranches.add(this);
                        addSATISFIER(notSatis);
                        break;
                    case AND:
                        And satisAnd = (And) satisProp;
                        applyAnd(expr, new Satisfier(satisNominal, satisAnd.propositionLeft),
                                new Satisfier(satisNominal, satisAnd.propositionRight), current, returnBranches,
                                TableauxRules.AND);
                        break;
                    case OR:
                        Or satisOr = (Or) satisProp;
                        applyOr(expr, new Satisfier(satisNominal, satisOr.propositionLeft),
                                new Satisfier(satisNominal, satisOr.propositionRight), current, returnBranches,
                                TableauxRules.OR);
                        break;
                    case SATISFIER:
                        TableauxPart satisSatis = new TableauxPart(satisProp, this.currentStep, current,
                                TableauxRules.SATIS);
                        addToBranch(satisSatis, true);
                        returnBranches.add(this);
                        
                        
                        break;
                    case DIAMOND:
                        
                        List<Nominal> SubFormNom = new ArrayList<>();
                        List<List<Nominal>> Refrence_a = new ArrayList<>();
                        List<Satisfier> nomIn = new ArrayList<>();

                        for(TableauxPart Snoms : tableauxParts){
                             
                            
                            if (Snoms.expr.getType() == ExpressionTypes.SATISFIER){
                                Satisfier noms = (Satisfier) Snoms.expr;
                                if(noms.proposition.getType() == ExpressionTypes.NOMINAL){
                                    nomIn.add(noms);
                                }
                            }
                            if (Snoms.expr.getType() == ExpressionTypes.NOT){
                                    Not Nnoms = (Not) Snoms.expr;
                                    if (Snoms.expr.getType() == ExpressionTypes.SATISFIER) {
                                        Satisfier noms = (Satisfier) Nnoms.proposition;
                                        if(noms.proposition.getType() == ExpressionTypes.NOMINAL){
                                            nomIn.add(noms);
                                        }
                                    }
                            }
                        }

                        
                        Diamond diamond = (Diamond) satisProp;
                        boolean diamondHasLoneNominal = diamond.proposition.getType() == ExpressionTypes.NOMINAL;
                        boolean branchHasDiamondRuleExpression = true;
                        for (int i = this.tableauxParts.size() - 1; i >= 0; i--) {
                            
                            if (tableauxParts.get(i).expr.getType() == ExpressionTypes.SATISFIER){
                                    
                                    Satisfier ree = (Satisfier) tableauxParts.get(i).expr;
                                    
                                    if (satisNominal.identifier.equals( ((Nominal) ree.referencePoint).identifier)){
                                        
                                        Refrence_a.add(( tableauxParts.get(i).seekLoopCondition(ree.proposition,satisNominal.identifier, false,nomIn, SubFormNom)));
                                    }
                                }

                            if (tableauxParts.get(i).expr.getType() == ExpressionTypes.NOT){
                                Not NotExpr = (Not) tableauxParts.get(i).expr;
                                if (tableauxParts.get(i).expr.getType() == ExpressionTypes.SATISFIER){
                                    
                                    Satisfier ree = (Satisfier) NotExpr.proposition;
                                    if (satisNominal.identifier.equals( ((Nominal) ree.referencePoint).identifier)){
                                        
                                        
                                        Refrence_a.add(tableauxParts.get(i).seekLoopCondition(ree.proposition,satisNominal.identifier, false,nomIn,SubFormNom));

                                    }
                                }
                            }
                        }
                        if (!Refrence_a.get(0).isEmpty()) {
                            
                        
                            for(int i = 0; i>Refrence_a.get(0).size(); i++){
                                for (int j = 0; j>Refrence_a.size(); j++){
                                    branchHasDiamondRuleExpression = branchHasDiamondRuleExpression && Refrence_a.get(j).contains( Refrence_a.get(0).get(i));
                                }
                            }
                        }else {branchHasDiamondRuleExpression = false;}
                        
                        if (!diamondHasLoneNominal && (!branchHasDiamondRuleExpression || AddLoopCheck)) {
                            String id = satisNominal.identifier;
                            String newNominalId = "D" + id + id;

                            TableauxPart newNominalSatis = new TableauxPart(
                                    new Satisfier(new Nominal(newNominalId), diamond.proposition), this.currentStep,
                                    current, TableauxRules.DIAMOND, current.lineNumber + 1);
                            addToBranch(newNominalSatis, true);
                            addSATISFIER(newNominalSatis);
                            TableauxPart newDiamondNominal = new TableauxPart(
                                    new Satisfier(satisNominal, new Diamond(new Nominal(newNominalId))),
                                    this.currentStep, current, TableauxRules.DIAMOND, current.lineNumber + 2);
                            addToBranch(newDiamondNominal, false);
                            addSATISFIER(newDiamondNominal);

                            newNominal(newNominalId, this.currentStep, newNominalSatis);
                        }
                        returnBranches.add(this);
                        
                        break;
                    case E:


                        List<Nominal> SubFormNomE = new ArrayList<>();
                        List<List<Nominal>> Refrence_aE = new ArrayList<>();
                        List<Satisfier> nomInE = new ArrayList<>();

                        for(TableauxPart Snoms : tableauxParts){
                             
                            
                            if (Snoms.expr.getType() == ExpressionTypes.SATISFIER){
                                Satisfier noms = (Satisfier) Snoms.expr;
                                if(noms.proposition.getType() == ExpressionTypes.NOMINAL){
                                    nomInE.add(noms);
                                }
                            }
                            if (Snoms.expr.getType() == ExpressionTypes.NOT){
                                    Not Nnoms = (Not) Snoms.expr;
                                    if (Snoms.expr.getType() == ExpressionTypes.SATISFIER) {
                                        Satisfier noms = (Satisfier) Nnoms.proposition;
                                        if(noms.proposition.getType() == ExpressionTypes.NOMINAL){
                                            nomInE.add(noms);
                                        }
                                    }
                            }
                        }

                        
                        E e = (E) satisProp;
                        boolean eHasLoneNominal = e.proposition.getType() == ExpressionTypes.NOMINAL;

                        boolean branchHasERuleExpression = true;
                        for (int i = this.tableauxParts.size() - 1; i >= 0; i--) {
                            
                            if (tableauxParts.get(i).expr.getType() == ExpressionTypes.SATISFIER){
                                    
                                    Satisfier ree = (Satisfier) tableauxParts.get(i).expr;
                                    
                                    if (satisNominal.identifier.equals( ((Nominal) ree.referencePoint).identifier)){
                                        
                                        Refrence_aE.add(tableauxParts.get(i).seekLoopCondition(ree.proposition,satisNominal.identifier, false,nomInE,SubFormNomE));
                                    }
                                }

                            if (tableauxParts.get(i).expr.getType() == ExpressionTypes.NOT){
                                Not NotExpr = (Not) tableauxParts.get(i).expr;
                                if (tableauxParts.get(i).expr.getType() == ExpressionTypes.SATISFIER){
                                   
                                    Satisfier ree = (Satisfier) NotExpr.proposition;
                                    if (satisNominal.identifier.equals( ((Nominal) ree.referencePoint).identifier)){
                                        
                                        Refrence_aE.add(tableauxParts.get(i).seekLoopCondition(ree.proposition,satisNominal.identifier, false,nomInE,SubFormNomE));

                                    }
                                }
                            }
                        }
                        
                        if (!Refrence_aE.get(0).isEmpty()) {
                            
                        
                            for(int i = 0; i>Refrence_aE.get(0).size(); i++){
                                for (int j = 0; j>Refrence_aE.size(); j++){
                                    branchHasERuleExpression = branchHasERuleExpression && Refrence_aE.get(j).contains( Refrence_aE.get(0).get(i));
                                }
                            }
                        }else {branchHasERuleExpression = false;}


                        if (!eHasLoneNominal && (!branchHasERuleExpression || AddLoopCheck)) {
                            String id = satisNominal.identifier;
                            TableauxPart newESatis = new TableauxPart(
                                    new Satisfier(new Nominal("E" + id + id), e.proposition), this.currentStep, current,
                                    TableauxRules.E);
                            addToBranch(newESatis, true);
                            addSATISFIER(newESatis);
                            newNominal("E" + id + id, this.currentStep, newESatis);
                        }
                        returnBranches.add(this);
                        
                        break;
                    case NOMINAL:
                        Nominal satisLoneNominal = (Nominal) satisProp;
                        if (!nomsInBranch.contains(satisLoneNominal.identifier)) {
                            newNominal(satisLoneNominal.identifier, current, current);
                            //addSATISFIER();
                        }
                        returnBranches.add(this);
                        
                        break;
                    case PROPOSITIONAL_SYMBOL:
                        returnBranches.add(this);
                        addSATISFIER(current);
                        break;
                    default:
                        System.err.println("Attempted to break down: " + current.expr
                                + " but encountered an unexpeted ExpressionType in Satisfier(...): "
                                + satisProp.getType());
                        returnBranches.add(this);
                        addSATISFIER(current);
                        break;
                }
                break;
            case NOT:
                Expression notProp = ((Not) expr).proposition;
                switch (notProp.getType()) {
                    case NOT:
                        Not notNot = (Not) notProp;
                        TableauxPart prop = new TableauxPart(notNot.proposition, this.currentStep, current,
                                TableauxRules.NOTNOT);
                        addToBranch(prop, true);
                        
                        returnBranches.add(this);
                        addSATISFIER(prop);
                        break;
                    case AND:
                        And notAnd = (And) notProp;
                        applyOr(expr, new Not(notAnd.propositionLeft), new Not(notAnd.propositionRight), current,
                                returnBranches, TableauxRules.NOTAND);
                        break;
                    case OR:
                        Or notOr = (Or) notProp;
                        applyAnd(expr, new Not(notOr.propositionLeft), new Not(notOr.propositionRight), current,
                                returnBranches, TableauxRules.NOTOR);
                        break;
                    case SATISFIER:
                        Satisfier notSatis = (Satisfier) notProp;
                        Nominal notSatisNominal = notSatis.referencePoint;
                        if (!nomsInBranch.contains(notSatisNominal.identifier)) {
                            newNominal(notSatisNominal.identifier, current, current);
                        }
                        if (notSatis.proposition.getType() == ExpressionTypes.NOT) {
                            Not notSatisNot = (Not) notSatis.proposition;
                            TableauxPart notNotSatis = new TableauxPart(
                                    new Satisfier(notSatis.referencePoint, notSatisNot.proposition), this.currentStep,
                                    current, TableauxRules.NOTNOT);
                            addToBranch(notNotSatis, true);
                            
                            returnBranches.add(this);
                            addSATISFIER(notNotSatis);
                        } else if (notSatis.proposition.getType() == ExpressionTypes.AND) {
                            And notSatisAnd = (And) notSatis.proposition;
                            applyOr(expr, new Not(new Satisfier(notSatis.referencePoint, notSatisAnd.propositionLeft)),
                                    new Not(new Satisfier(notSatis.referencePoint, notSatisAnd.propositionRight)),
                                    current, returnBranches, TableauxRules.NOTAND);
                        } else if (notSatis.proposition.getType() == ExpressionTypes.OR) {
                            Or notSatisOr = (Or) notSatis.proposition;
                            applyAnd(expr, new Not(new Satisfier(notSatis.referencePoint, notSatisOr.propositionLeft)),
                                    new Not(new Satisfier(notSatis.referencePoint, notSatisOr.propositionRight)),
                                    current, returnBranches, TableauxRules.NOTOR);
                        } else if (notSatis.proposition.getType() == ExpressionTypes.SATISFIER) {
                            Satisfier notSatisSatis = (Satisfier) notSatis.proposition;
                            TableauxPart innerNotSatis = new TableauxPart(new Not(notSatisSatis), this.currentStep,
                                    current, TableauxRules.NOTSATIS);
                            addToBranch(innerNotSatis, true);
                            returnBranches.add(this);
                            addSATISFIER(innerNotSatis);
                        } else if (notSatis.proposition.getType() == ExpressionTypes.DIAMOND) {
                            applyNotDiamond(current);
                            notDiamondInEffect = true;
                            origNotDiamondParts.add(current);
                            returnBranches.add(this);
                            addSATISFIER(current);
                        } else if (notSatis.proposition.getType() == ExpressionTypes.E) {
                            applyNotE(current, notSatis.referencePoint);
                            this.notEInEffect = true;
                            this.origNotEParts.add(current);
                        } else if (notSatis.proposition.getType() == ExpressionTypes.NOMINAL) {
                            Nominal satisLoneNominal = (Nominal) notSatis.proposition;
                            if (!nomsInBranch.contains(satisLoneNominal.identifier)) {
                                newNominal(satisLoneNominal.identifier, current, current);
                                //addSATISFIER(current);
                            }
                            returnBranches.add(this);
                        } else if (notSatis.proposition.getType() == ExpressionTypes.PROPOSITIONAL_SYMBOL) {
                            returnBranches.add(this);
                            //
                        } else {
                            System.err.println("Attempted to break down: " + current.expr
                                    + " but encountered unexpected Expression type in Not(Satisfier(...)): "
                                    + notSatis.proposition.getType());

                            returnBranches.add(this);
                            addSATISFIER(current);
                        }
                        break;
                    case NOMINAL:
                        Nominal notNominal = (Nominal) notProp;
                        if (!nomsInBranch.contains(notNominal.identifier)) {
                            newNominal(notNominal.identifier, current, current);
                        }
                        break;
                    default:
                        System.err.println("Attempted to break down: " + current.expr
                                + "but encountered an unexpeted ExpressionType in Not(...):" + notProp.getType());
                        returnBranches.add(this);
                        addSATISFIER(current);
                        break;
                }
                break;
            case NOMINAL:
                Nominal nominal = (Nominal) expr;
                if (!nomsInBranch.contains(nominal.identifier)) {
                    newNominal(nominal.identifier, current, current);
                }
                break;
            default:
                System.err.println("Attempted to break down: " + current.expr
                        + "but encountered an unexpeted ExpressionType: " + type);
                returnBranches.add(this);
                addSATISFIER(current);
                break;
        }

        return returnBranches;
    }

    public String toString() {
        LinkedList<String> s = new LinkedList<>();
        TableauxPart next = this.currentStep;
        while (next != null) {
            s.add(next.toString());
            if (tableauxParts.contains(next.from)) {
                next = next.from;
            } else
                next = null;
        }
        String string = "";
        for (int i = s.size() - 1; i >= 0; i--) {
            string += "\n " + s.get(i);
        }
        return string;
    }

}

class TableauxPart {
    Expression expr;
    TableauxPart from;
    TableauxPart source;
    int lineNumber;
    TableauxRules ruleApplied;
    boolean contradiction = false;

    // Line number set explicidly
    public TableauxPart(Expression e, TableauxPart from, TableauxPart source, TableauxRules ruleApplied,
            int lineNumber) {
        this.expr = e;
        // From is a reference to the "step" it is from, it has nothing to do with what
        // expression the current tableauxPart is a subexpression of
        this.from = from;
        // Souce is the expression this tableaux part is made from
        this.source = source;
        // Set the line number
        this.lineNumber = lineNumber;
        // Rule applied to get this tableauxPart
        this.ruleApplied = ruleApplied;
    }

    // Line number gotten from from
    public TableauxPart(Expression e, TableauxPart from, TableauxPart source, TableauxRules ruleApplied) {
        this.expr = e;
        // From is a reference to the "step" it is from, it has nothing to do with what
        // expression the current tableauxPart is a subexpression of
        this.from = from;
        // Souce is the expression this tableaux part is made from
        this.source = source;
        // Set the line number
        if (from == null) {
            this.lineNumber = 1;
        } else
            this.lineNumber = from.lineNumber + 1;
        // Rule applied to get this tableauxPart
        this.ruleApplied = ruleApplied;
    }

    public String toString() {
        if (from != null && source != null) {
            return expr.toString() + "\t" + "Line: " + lineNumber + ", Rule: " + ruleApplied + " from: "
                    + source.lineNumber;
        }
        return expr.toString() + "\t" + "Line: " + lineNumber;
    }

    public boolean seekExpressionInBranch(Expression model) {
        if (expr.equals(model)) {
            return true;
        }
        if (from == null) {
            return false;
        }
        return from.seekExpressionInBranch(model);
    }

    public LinkedList<Satisfier> seekAllNominalRelations(String targetId, LinkedList<Satisfier> foundRelation) {
        LinkedList<Satisfier> returnNoms = foundRelation;
        if (foundRelation == null) {
            returnNoms = new LinkedList<>();
        }
        if (expr.getType() == ExpressionTypes.SATISFIER) {
            Satisfier inner = (Satisfier) expr;
            Boolean isLoneNominal = inner.proposition.getType() == ExpressionTypes.NOMINAL;
            Boolean isTargetReference = inner.referencePoint.identifier.equals(targetId);
            if (isLoneNominal && isTargetReference) {
                returnNoms.add(inner);
            }
        }
        if (from == null) {
            return returnNoms;
        }
        return from.seekAllNominalRelations(targetId, returnNoms);
    }

    public LinkedList<Satisfier> seekAllNomRuleFormula(String targetId, LinkedList<Satisfier> foundNomRuleFormula) {
        LinkedList<Satisfier> returnNoms = foundNomRuleFormula;
        if (foundNomRuleFormula == null) {
            returnNoms = new LinkedList<>();
        }
        if (expr.getType() == ExpressionTypes.SATISFIER) {
            Satisfier inner = (Satisfier) expr;
            Boolean isLoneNominal = inner.proposition.getType() == ExpressionTypes.NOMINAL;
            Boolean isLonePropSymbol = inner.proposition.getType() == ExpressionTypes.PROPOSITIONAL_SYMBOL;
            Boolean isDiamond = inner.proposition.getType() == ExpressionTypes.DIAMOND;
            Boolean diamondHasLonePropSymbol = false;
            if (isDiamond) {
                diamondHasLonePropSymbol = ((Diamond) inner.proposition).proposition
                        .getType() == ExpressionTypes.NOMINAL;
            }
            Boolean isTargetReference = inner.referencePoint.identifier.equals(targetId);
            if (((isDiamond && diamondHasLonePropSymbol) || isLonePropSymbol || isLoneNominal) && isTargetReference) {
                returnNoms.add(inner);
            }
        }
        if (from == null) {
            return returnNoms;
        }
        return from.seekAllNomRuleFormula(targetId, returnNoms);
    }

    public List<Nominal> seekLoopCondition(Expression target, String selfId, Boolean rightTargetRightNominal, List<Satisfier> nominalInBranch, List<Nominal> returnSubFormNom) {
        Boolean flag = rightTargetRightNominal;
        
        

        if (expr.getType() == ExpressionTypes.SATISFIER) {
            Satisfier inner = (Satisfier) expr;
            
            Boolean isOwnNominal = ((Nominal) inner.referencePoint).identifier.equals(selfId);
            Boolean isTarget = inner.proposition.equals(target);
            
            if ((inner.referencePoint.identifier).toString().equals((inner.proposition).toString())){
                for(int j = nominalInBranch.size() - 1; j >= 0; j--) {
                    Satisfier bret = (Satisfier) nominalInBranch.get(j);
                    Boolean isOwnNominalNominal = (((Nominal) bret.referencePoint).identifier).equals(selfId);
                    Boolean isTargetNominal = inner.proposition.equals(target);
                    if (isTargetNominal && !isOwnNominalNominal){
                        
                        
                        
                        returnSubFormNom.add(bret.referencePoint );
                        
                    }
                }
                return returnSubFormNom;
            }

            if (isTarget && !isOwnNominal && rightTargetRightNominal) {
                returnSubFormNom.add(inner.referencePoint);
                return returnSubFormNom;
            } else if (isTarget && isOwnNominal) {
                flag = true;
            }
        } else if (expr.getType() == ExpressionTypes.NOT) {
            Not inner = (Not) expr;
            if (inner.proposition.getType() == ExpressionTypes.SATISFIER) {
                Satisfier notInner = (Satisfier) inner.proposition;
                Boolean isOwnNominal = ((Nominal) notInner.referencePoint).identifier.equals(selfId);
                Boolean isTarget = notInner.proposition.equals(target);

                if ((notInner.referencePoint).toString().equals((notInner.proposition).toString())){
                    for(int j = nominalInBranch.size() - 1; j >= 0; j--) {
                        Satisfier bret = (Satisfier) nominalInBranch.get(j);
                        Boolean isOwnNominalNominal = (((Nominal) bret.referencePoint).identifier).equals(selfId);
                        Boolean isTargetNominal = inner.proposition.equals(target);
                        if (isTargetNominal && !isOwnNominalNominal){
                            
                            returnSubFormNom.add(bret.referencePoint);
                            
                        }
                    }
                    return returnSubFormNom;
                }

                if (isTarget && !isOwnNominal && rightTargetRightNominal) {
                    returnSubFormNom.add(notInner.referencePoint);
                    return returnSubFormNom;
                } else if (isTarget && isOwnNominal) {
                    flag = true;
                }
            }
        }
        if (from == null) {
            return returnSubFormNom;
        }
        return from.seekLoopCondition(target, selfId, flag, nominalInBranch,returnSubFormNom);
    }

    public Nominal seekNotDiamondRule(String nominalID) {
        if (expr.getType() == ExpressionTypes.SATISFIER) {
            Satisfier inner = (Satisfier) expr;
            Nominal nominal = (Nominal) inner.referencePoint;
            if (nominal.identifier.equals(nominalID) && inner.proposition.getType() == ExpressionTypes.DIAMOND) {
                Diamond innerInner = (Diamond) inner.proposition;
                if (innerInner.proposition.getType() == ExpressionTypes.NOMINAL) {
                    return (Nominal) innerInner.proposition;
                }
            }
        }
        if (from == null) {
            return null;
        }
        return from.seekNotDiamondRule(nominalID);
    }
}

enum TableauxRules {
    AND,
    OR,
    NOTNOT,
    NOTOR,
    NOTAND,
    NOT,
    SATIS,
    NOTSATIS,
    DIAMOND,
    NOTDIAMOND,
    E,
    NOTE,
    REF,
    NOM1,
    NOM2
}