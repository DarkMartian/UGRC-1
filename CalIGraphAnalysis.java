package testing;

import java.util.*;
import soot.tagkit.StringTag;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.jimple.spark.ondemand.AllocAndContextSet;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.pag.AllocNode;
import soot.jimple.spark.sets.DoublePointsToSet;
import soot.jimple.spark.sets.EmptyPointsToSet;
import soot.jimple.spark.sets.PointsToSetInternal;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.Type;
import soot.Unit;
import soot.UnitPatchingChain;
import soot.Value;
import soot.ValueBox;
import soot.dava.internal.AST.ASTTryNode.container;
import soot.Body;
import soot.BodyTransformer;
import soot.Context;
import soot.EntryPoints;
import soot.Local;
import soot.LocalGenerator;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.GotoStmt;
import soot.jimple.ThrowStmt;
import soot.jimple.SwitchStmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewArrayExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JNewMultiArrayExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MutableDirectedGraph;
import soot.toolkits.graph.UnitGraph;
import soot.javaToJimple.*;
// Added imports for Liveness Analysis
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.LiveLocals;

public class CalIGraphAnalysis extends SceneTransformer{
	static boolean debug = false;
	
	class methodLocal {
		SootMethod m;
		JimpleLocal l;
		
		public methodLocal(SootMethod m_, JimpleLocal l_) {
			m = m_;
			l = l_;
		}
		
		@Override
		public String toString() {
			return "\nMethod: " + m.toString() + " Local: " + l.toString();
		}
	}
	
	class blockNode{
		Unit unit;
		
		SootMethod containingMethod;
		
		HashSet<Integer> in, out;
		
		Vector<blockNode> succ;

		// create constructor
		blockNode(Unit u, SootMethod sm) {
			unit = u;
			containingMethod = sm;
			
			in = null;
			out = null;
			succ = new Vector<blockNode>();
		}
	}
	
	public class PrintableHashMap<K, V> extends HashMap<K, V>{
		@Override
		public String toString() {
			String s = "";
			
			for(Entry<K, V> entry : entrySet()) {
				s += entry.getKey() + " :\n";
				if(entry.getValue() instanceof Vector) {
					for(Object o : (Vector) entry.getValue()) {
						s += "    " + o + "\n";
					}
				}
				else if(entry.getValue() instanceof HashSet) {
					for(Object o : (HashSet) entry.getValue()) {
						s += "    " + o + "\n";
					}
				}
				else {
					s += "    " + entry.getValue() + "\n";
				}
			}
			
			return s;
		}
	}
	
	PrintableHashMap<SootClass, SootClass> parent = new PrintableHashMap<SootClass, SootClass>();
	PrintableHashMap<SootClass, Vector<SootClass>> child = new PrintableHashMap<SootClass, Vector<SootClass>>();
	PrintableHashMap<SootMethod, Vector<SootMethod>> overloadedMethods = new PrintableHashMap<SootMethod, Vector<SootMethod>>();
	
	PrintableHashMap<Integer, Vector<methodLocal>> object2local = new PrintableHashMap<Integer, Vector<methodLocal>>();
	PrintableHashMap<methodLocal, Vector<Integer>> local2object = new PrintableHashMap<methodLocal, Vector<Integer>>();
	PrintableHashMap<Integer, PrintableHashMap<SootField, Vector<Integer>>> object2object = new PrintableHashMap<Integer, PrintableHashMap<SootField, Vector<Integer>>>();
	PrintableHashMap<Integer, PrintableHashMap<SootField, Vector<Integer>>> object2object2 = new PrintableHashMap<Integer, PrintableHashMap<SootField, Vector<Integer>>>();
	PrintableHashMap<SootMethod, HashSet<Integer>> methodCreates = new PrintableHashMap<SootMethod, HashSet<Integer>>();
	PrintableHashMap<SootMethod, HashSet<Integer>> methodUses = new PrintableHashMap<SootMethod, HashSet<Integer>>();
	
	HashMap<SootMethod, Vector<blockNode>> methodGraph = new HashMap<SootMethod, Vector<blockNode>>();
	HashMap<SootMethod, Vector<blockNode>> methodHeads = new HashMap<SootMethod, Vector<blockNode>>();
	HashMap<SootMethod, blockNode> methodReturns = new HashMap<SootMethod, blockNode>();
	PrintableHashMap<SootMethod, HashSet<Integer>> methodKilled = new PrintableHashMap<SootMethod, HashSet<Integer>>();


	HashMap<SootMethod, Boolean> freeingVisited = new HashMap<SootMethod, Boolean>();
	// methodKilled gives the set of objects killed in each method

	// Counter for unique temp-local names emitted by findPointerRec.
	int tempCounter = 0;

	// Stored at internalTransform time so helper methods can use it without threading it everywhere
	PointsToAnalysis pta;

	@Override
	protected void internalTransform(String arg0, Map<String, String> arg1) {
		CallGraph cg = Scene.v().getCallGraph();
		PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
		this.pta = pta;
		
		// get the parent class relations
		for(SootClass sc : Scene.v().getApplicationClasses()) {
			if(sc.getName().startsWith("jdk", 0)) continue;
			
			if(sc.hasSuperclass()) {
				SootClass superClass = null;
				if(!sc.getSuperclass().getName().equals("java.lang.Object"))
					superClass = sc.getSuperclass();
				
				parent.put(sc, superClass);
			}
		}
		
		for(SootClass sc : parent.keySet()) {
			SootClass parentClass = parent.get(sc);
			
			if(parentClass != null) {
				if(!child.containsKey(parentClass)) child.put(parentClass, new Vector<SootClass>());
				
				child.get(parentClass).add(sc);
			}
		}
		
		for(SootClass sc : child.keySet()) {
			for(SootMethod sm : sc.getMethods()) {
				String name = sm.getName();
				List<Type> paramTypes = sm.getParameterTypes();
				Type retType = sm.getReturnType();
				
				Queue<SootClass> childs = new LinkedList<SootClass>();
				for(SootClass childClass : child.get(sc)) childs.add(childClass);
				
				while(!childs.isEmpty()) {
					SootClass childClass = childs.poll();
					
					if(childClass.declaresMethod(name, paramTypes, retType)) {
						SootMethod childMethod = childClass.getMethod(name, paramTypes, retType);
						
						if(!overloadedMethods.containsKey(sm)) overloadedMethods.put(sm, new Vector<SootMethod>());
						overloadedMethods.get(sm).add(childMethod);
					}
					
					if(child.containsKey(childClass)) {
						for(SootClass next : child.get(childClass)) childs.add(next);
					}
				}
			}
		}
		
		SootMethod mainMethod = Scene.v().getMainMethod();
		
		iterateCallGraph(cg, pta, mainMethod, new HashMap<SootMethod, Boolean>());
		
		
		for(Integer o1 : object2object.keySet()) {
			for(SootField f : object2object.get(o1).keySet()) {
				for(Integer o2 : object2object.get(o1).get(f)) {
					if(!object2object2.containsKey(o2)) object2object2.put(o2, new PrintableHashMap<SootField, Vector<Integer>>());
					
					if(!object2object2.get(o2).containsKey(f)) object2object2.get(o2).put(f, new Vector<Integer>());
					
					object2object2.get(o2).get(f).add(o1);
				}
			}
		}
		
		
		if(debug) {
			System.out.println("Child classes:");
			System.out.println(child);
			System.out.println("------------------------------------------------------------------------------------");
			System.out.println("Overloaded Methods");
			System.out.println(overloadedMethods);
			System.out.println("------------------------------------------------------------------------------------");
			System.out.println("Local to Object Map:");
			System.out.println(local2object);
			System.out.println("------------------------------------------------------------------------------------");
			System.out.println("Object to Local Map:");
			System.out.println(object2local);
			System.out.println("------------------------------------------------------------------------------------");
			System.out.println("Object to Object Map:");
			System.out.println(object2object2);
			System.out.println("------------------------------------------------------------------------------------");
			System.out.println("Objects created in every method");
			System.out.println(methodCreates);
			System.out.println("------------------------------------------------------------------------------------");
			System.out.println("Objects used in every method");
			System.out.println(methodUses);
			System.out.println("------------------------------------------------------------------------------------");
		}

		createMethodGraph();
		
		// Sorted method list – used everywhere we iterate methodGraph so that
		// debug output and analysis always visit methods in a deterministic,
		// lexicographic order by method signature.
		List<SootMethod> sortedMethods = new ArrayList<SootMethod>(methodGraph.keySet());
		Collections.sort(sortedMethods, (a, b) -> a.getSignature().compareTo(b.getSignature()));

		if(debug) {
			for(SootMethod sm: sortedMethods) {
				// for each blockNode in the methodGraph, print successors
				System.out.println("------------------------------------------------------------------------------------");
				System.out.println("Method: " + sm);
				for(blockNode bn: methodGraph.get(sm)) {
					System.out.println("Unit: " + bn.unit + bn.unit.getTags().toString());
					System.out.println("Successors: ");
					for(blockNode succ: bn.succ) {
						System.out.println("    " + succ.unit + succ.unit.getTags().toString());
					}
				}
				System.out.println();
			}
			System.out.println("------------------------------------------------------------------------------------");
		}

		simplifyMethodGraphs();

		// Re-sort after simplification in case new methods were inserted.
		sortedMethods = new ArrayList<SootMethod>(methodGraph.keySet());
		Collections.sort(sortedMethods, (a, b) -> a.getSignature().compareTo(b.getSignature()));
		
		if(debug) {
			for(SootMethod sm: sortedMethods) {
				// for each blockNode in the methodGraph, print successors
				System.out.println("------------------------------------------------------------------------------------");
				System.out.println("Method: " + sm);
				for(blockNode bn: methodGraph.get(sm)) {
					System.out.println("Unit: " + bn.unit + bn.unit.getTags().toString());
					System.out.println("Successors: ");
					for(blockNode succ: bn.succ) {
						System.out.println("    " + succ.unit + succ.unit.getTags().toString());
					}
				}
				System.out.println();
			}
			System.out.println("------------------------------------------------------------------------------------");
		}
		
		performContextInsensitiveAnalysis();

		if(debug) {
			for(SootMethod sm: sortedMethods) {
				// for each blockNode in the methodGraph, print successors
				System.out.println("------------------------------------------------------------------------------------");
				System.out.println("Method: " + sm);
				for(blockNode bn: methodGraph.get(sm)) {
					System.out.println("Unit: " + bn.unit + bn.unit.getTags().toString());
					System.out.println("Out");
					System.out.println(bn.out);
					System.out.println("In");
					System.out.println(bn.in);
				}
				System.out.println();
			}
			System.out.println("------------------------------------------------------------------------------------");
		}
		
		if(debug) {
			System.out.println("Objects killed in each method:");
			System.out.println(methodKilled);
		}

		// =========================================================================
		// Safe-Local Null Insertion + Field-Link Freeing
		//
		// For each method we:
		//   1. Use methodKilled (= (in ∪ created) − out) as the kill set.
		//   2. Find safe locals – non-parameter locals whose entire PTA set is
		//                         within the kill set.
		//   3. Backward liveness for locals → localNullInsertions.
		//   4. Apply local-null insertions.
		//   5. Call freeLinks(killSet, sm) to null dead field links at return
		//      (args / this only, findPointer singleton rule).
		// =========================================================================
		if(debug) {
			System.out.println("------------------------------------------------------------------------------------");
			System.out.println("Starting Safe-Local + freeLinks Analysis");
		}

		for(SootMethod sm : sortedMethods) {
			if (!sm.hasActiveBody()) continue;
			Body body = sm.getActiveBody();
			UnitPatchingChain units = body.getUnits();

			// ------------------------------------------------------------------
			// Step 1 – Kill set: methodKilled = (in ∪ created) − out, computed
			//           once in performContextInsensitiveAnalysis and reused here.
			// ------------------------------------------------------------------
			if (!methodKilled.containsKey(sm)) continue;
			HashSet<Integer> killSet = methodKilled.get(sm);
			if (killSet.isEmpty()) continue;

			if(debug) {
				System.out.println("Method: " + sm.getName());
				System.out.println("  Kill Set: " + killSet);
			}

			// ------------------------------------------------------------------
			// Step 2 – Identify parameter / this locals (excluded from local
			//           null insertion; they belong to the caller)
			// ------------------------------------------------------------------
			HashSet<Local> parameterLocals = new HashSet<Local>();
			for(Unit u : units) {
				if(u instanceof IdentityStmt) {
					IdentityStmt is = (IdentityStmt) u;
					if(is.getRightOp() instanceof ParameterRef || is.getRightOp() instanceof ThisRef) {
						if(is.getLeftOp() instanceof Local)
							parameterLocals.add((Local) is.getLeftOp());
					}
				}
			}

			// ------------------------------------------------------------------
			// Step 3 – Safe locals: non-parameter, entire PTA ⊆ killSet
			// ------------------------------------------------------------------
			HashSet<Local> safeLocals = new HashSet<Local>();
			for(methodLocal ml : local2object.keySet()) {
				if(ml.m != sm) continue;
				if(parameterLocals.contains(ml.l)) continue;

				Vector<Integer> pointsTo = local2object.get(ml);
				if(pointsTo.isEmpty()) continue;

				boolean allInKill = true;
				for(Integer obj : pointsTo) {
					if(!killSet.contains(obj)) { allInKill = false; break; }
				}
				if(allInKill) safeLocals.add(ml.l);
			}

			if(debug && !safeLocals.isEmpty())
				System.out.println("  Safe Locals: " + safeLocals);

			// ------------------------------------------------------------------
			// Step 4 – Backward local liveness → localNullInsertions.
			//
			// For each safe (non-parameter) local l, find the last unit in the
			// body that uses l.  Insert  l = null  immediately after that unit
			// so the GC can reclaim the object as early as possible.
			// ------------------------------------------------------------------
			if (!safeLocals.isEmpty()) {
				ExceptionalUnitGraph cfg = new ExceptionalUnitGraph(body);
				LiveLocals liveLocals = new SimpleLiveLocals(cfg);
				List<Map.Entry<Unit, Local>> localNullInsertions =
					new ArrayList<Map.Entry<Unit, Local>>();

				for (Unit u : units) {
					if (u instanceof IfStmt      || u instanceof GotoStmt   ||
					    u instanceof SwitchStmt  || u instanceof ReturnStmt ||
					    u instanceof ReturnVoidStmt || u instanceof RetStmt ||
					    u instanceof ThrowStmt) continue;

					for (ValueBox vb : u.getUseBoxes()) {
						Value v = vb.getValue();
						if (!(v instanceof Local)) continue;
						Local l = (Local) v;
						if (!safeLocals.contains(l)) continue;

						if (!liveLocals.getLiveLocalsAfter(u).contains(l)) {
							localNullInsertions.add(
								new AbstractMap.SimpleEntry<Unit, Local>(u, l));
							if (debug)
								System.out.println("  Local last use: " + l + "  at: " + u);
						}
					}
				}

				// ------------------------------------------------------------------
				// Step 5 – Insert local nulls immediately after their last-use unit.
				// ------------------------------------------------------------------
				for (Map.Entry<Unit, Local> e : localNullInsertions) {
					try {
						Unit anchor     = e.getKey();
						Unit nullAssign = Jimple.v().newAssignStmt(e.getValue(), NullConstant.v());
						units.insertAfter(nullAssign, anchor);

						if (debug)
							System.out.println("  [local-null]  " + e.getValue()
								+ " = null  after: " + anchor);
					} catch (Exception ex) {
						if (debug)
							System.out.println("  [local-null]  FAILED for "
								+ e.getValue() + ": " + ex.getMessage());
					}
				}
			}

			// ------------------------------------------------------------------
			// Step 6 – Free dead field links at method return.
			//
			// freeLink(sm, killSet, liveObjIn, liveObjOut, safeLocals) frees
			// field links based on object liveness. Called AFTER safeLocals is
			// computed so the analysis is consistent with the set built above.
			// ------------------------------------------------------------------
			if (!killSet.isEmpty()) {
				// Compute object liveness for this method
				ObjectLivenessResult liveness = computeObjectLiveness(sm);
				
				// Call freeLink with the liveness information and excluded (safe) locals
				freeLink(sm, killSet, liveness.liveObjIn, liveness.liveObjOut, safeLocals);
			}

		}
		// =========================================================================
		// end of unified analysis
		// =========================================================================
		
		for(SootMethod sm : sortedMethods) {
			System.out.println(sm.getActiveBody());
		}
		
	}
	
	
	void iterateCFG(SootMethod rootMethod, PointsToAnalysis pta) {
		Boolean debug = false;
		if(debug) {
			System.out.println("------------------------------------------------------------------------------------");
			System.out.println(rootMethod);
		}
		
		for(Local l : rootMethod.getActiveBody().getLocals()) {
			
			if(debug) {
				System.out.println("\n" + l);
				System.out.println(l.getType());
				System.out.println(l.getType().getClass().getClass());
			}
			
			PointsToSet pts = pta.reachingObjects(l);
			
			if(pts instanceof EmptyPointsToSet) continue;
			
			methodLocal ml = new methodLocal(rootMethod, (JimpleLocal) l);
			
			Vector<Integer> v = new Vector<Integer>();
			((DoublePointsToSet) pts).forall( new P2SetVisitor() {
				
				@Override
				public void visit(Node n) {
					if(!object2local.containsKey(n.getNumber())) {
						object2local.put(n.getNumber(), new Vector<methodLocal>());
					}
					object2local.get(n.getNumber()).add(ml);
					
					v.add(n.getNumber());
				}
			});
			
			local2object.put(ml, v);
		}
		
		ExceptionalUnitGraph g = new ExceptionalUnitGraph(rootMethod.retrieveActiveBody());
		
		HashMap<Unit, Boolean> visited_unit = new HashMap<Unit, Boolean>();
		
		HashSet<Integer> creates = new HashSet<Integer>();
		HashSet<Integer> uses = new HashSet<Integer>();
		
		Queue<Unit> q = new LinkedList<Unit>();
		
		Vector<blockNode> blockHeads = new Vector<blockNode>();
		
		for(Unit head : g.getHeads()) {
			q.add(head);
			
			blockNode bn = new blockNode(head, rootMethod);
			blockHeads.add(bn);
		}
		
		while(!q.isEmpty()) {
			Unit cur = q.poll();
			
			if(visited_unit.containsKey(cur))
				continue;
		
			visited_unit.put(cur, true);
			
			Stmt s = (Stmt) cur;
			
			for(Unit next : g.getSuccsOf(cur))
				q.add(next);
			
			if(debug) {
				System.out.println();
				System.out.println(s);
				System.out.println(s.getClass());
				System.out.println("Use Boxes");
				for(ValueBox vb : s.getUseBoxes()) {
					System.out.println(vb.getValue() + " - " + vb.getValue().getClass());
				}
				System.out.println("Def Boxes");
				for(ValueBox vb : s.getDefBoxes()) {
					System.out.println(vb.getValue() + " - " + vb.getValue().getClass());
				}
			}
			
			Boolean hasInvocation = false;
			List<Value> args = null;
			for(ValueBox vb : s.getUseBoxes()) {
				if(vb.getValue() instanceof InvokeExpr) {
					hasInvocation = true;
					args = ((InvokeExpr) vb.getValue()).getArgs();
					break;
				}
			}
			
			if(debug && hasInvocation) {
				for(Value v : args) {
					System.out.println("Arg : " + v);
				}
			}
			
			for(ValueBox vb : s.getUseBoxes()) {
				if(vb.getValue() instanceof ParameterRef) {
					JimpleLocal l = (JimpleLocal) s.getDefBoxes().get(0).getValue();
					PointsToSet pts = pta.reachingObjects(l);
					
					if(!(pts instanceof EmptyPointsToSet)) {
					
						((DoublePointsToSet) pts).forall(new P2SetVisitor() {
							
							@Override
							public void visit(Node n) {
								uses.add(n.getNumber());
								if(debug)
									System.out.println("Added " + n.getNumber() + " to use set");
							}
						});
					}
				}
				else if(vb.getValue() instanceof ThisRef) {
					JimpleLocal l = (JimpleLocal) s.getDefBoxes().get(0).getValue();
					
					if(l.getName().startsWith("temp")) continue;
					
					PointsToSet pts = pta.reachingObjects(l);
					
					if(!(pts instanceof EmptyPointsToSet)) {
					
						((DoublePointsToSet) pts).forall(new P2SetVisitor() {
							
							@Override
							public void visit(Node n) {
								uses.add(n.getNumber());
								if(debug)
									System.out.println("Added " + n.getNumber() + " to use set");
							}
						});
					}
				}
				else if(vb.getValue() instanceof JimpleLocal) {
					JimpleLocal l = (JimpleLocal) vb.getValue();
					
					if(l.getName().startsWith("temp$")) continue;
					
					PointsToSet pts = pta.reachingObjects(l);
					
					if(!(pts instanceof EmptyPointsToSet)) {
					
						((DoublePointsToSet) pts).forall(new P2SetVisitor() {
							
							@Override
							public void visit(Node n) {
								uses.add(n.getNumber());
								if(debug)
									System.out.println("Added " + n.getNumber() + " to use set");
							}
						});
					}
				}
				else if(vb.getValue() instanceof JInstanceFieldRef) {					
					JimpleLocal l = (JimpleLocal) ((JInstanceFieldRef) vb.getValue()).getBase();
					SootField f = (SootField) ((JInstanceFieldRef) vb.getValue()).getField();
					
					PointsToSet pts = pta.reachingObjects(l);
					Vector<Integer> pointsTo_l = new Vector<Integer>();
					if(!(pts instanceof EmptyPointsToSet)) {
						
						((DoublePointsToSet) pts).forall(new P2SetVisitor() {
							
							@Override
							public void visit(Node n) {
								pointsTo_l.add(n.getNumber());
								uses.add(n.getNumber());
							}
						});
					}
					
					pts = pta.reachingObjects(l, f);
					
					for(Integer o : pointsTo_l) {
						if(!object2object.containsKey(o))
							object2object.put(o, new PrintableHashMap<SootField, Vector<Integer>>());
						
						if(!object2object.get(o).containsKey(f))
							object2object.get(o).put(f, new Vector<Integer>());
					}
					
					if(!(pts instanceof EmptyPointsToSet)) {
						((DoublePointsToSet) pts).forall(new P2SetVisitor() {
							
							@Override
							public void visit(Node n) {
								for(Integer o : pointsTo_l) {
									// Guard against duplicates: multiple aliased locals
									// can point to the same base object, causing the same
									// target to be added more than once.
									if(!object2object.get(o).get(f).contains(n.getNumber()))
										object2object.get(o).get(f).add(n.getNumber());
									uses.add(n.getNumber());
								}
							}
						});
					}
				}
				else if(vb.getValue() instanceof JNewExpr || vb.getValue() instanceof JNewArrayExpr || vb.getValue() instanceof JNewMultiArrayExpr) {
					JimpleLocal l = (JimpleLocal) (((DefinitionStmt) s).getLeftOp());
					
					PointsToSet pts = pta.reachingObjects(l);
					
					if(!(pts instanceof EmptyPointsToSet)) {
					
						((DoublePointsToSet) pts).forall(new P2SetVisitor() {
							
							@Override
							public void visit(Node n) {
								creates.add(n.getNumber());
							}
						});
					}
				}
			}

			// Scan def boxes for field writes:  a.f = something
			// JInstanceFieldRef only appears in use boxes for reads (x = a.f).
			// For writes (a.f = x) it is in the def box, so we must handle it
			// here separately to populate object2object correctly.
			//
			// Note: In standard Soot/Jimple the base local `a` of a LHS field ref
			// DOES appear in the statement's use boxes (JInstanceFieldRef exposes its
			// base as a use).  We still handle it here so that:
			//   (a) object2object is correctly populated for field writes, and
			//   (b) we don't rely on a particular Soot version's use-box exposure.
			for(ValueBox vb : s.getDefBoxes()) {
				if(!(vb.getValue() instanceof JInstanceFieldRef)) continue;

				JimpleLocal l = (JimpleLocal) ((JInstanceFieldRef) vb.getValue()).getBase();
				SootField   f = (SootField)   ((JInstanceFieldRef) vb.getValue()).getField();

				PointsToSet pts = pta.reachingObjects(l);
				Vector<Integer> pointsTo_l = new Vector<Integer>();
				if(!(pts instanceof EmptyPointsToSet)) {
					((DoublePointsToSet) pts).forall(new P2SetVisitor() {
						@Override
						public void visit(Node n) {
							pointsTo_l.add(n.getNumber());
							uses.add(n.getNumber());   // base is dereferenced → counts as use
						}
					});
				}

				// Ensure entries exist before trying to fill them
				for(Integer o : pointsTo_l) {
					if(!object2object.containsKey(o))
						object2object.put(o, new PrintableHashMap<SootField, Vector<Integer>>());
					if(!object2object.get(o).containsKey(f))
						object2object.get(o).put(f, new Vector<Integer>());
				}

				// pta.reachingObjects(l, f) is flow-insensitive and returns all
				// objects that a.f can point to across the whole program,
				// including the object written here.
				pts = pta.reachingObjects(l, f);
				if(!(pts instanceof EmptyPointsToSet)) {
					((DoublePointsToSet) pts).forall(new P2SetVisitor() {
						@Override
						public void visit(Node n) {
							for(Integer o : pointsTo_l) {
								// Guard against duplicates introduced when multiple aliased
								// locals share the same base object (e.g. both `a` and `b`
								// → O1, and both `a.f=x` and `b.f=x` are visited).
								if(!object2object.get(o).get(f).contains(n.getNumber()))
									object2object.get(o).get(f).add(n.getNumber());
								uses.add(n.getNumber());
							}
						}
					});
				}
			}
		}
		
		methodCreates.put(rootMethod, creates);
		methodUses.put(rootMethod, uses);
		
		methodHeads.put(rootMethod, blockHeads);
		methodGraph.put(rootMethod, new Vector<blockNode>()); 
	}
	
	
	void iterateCallGraph(CallGraph cg, PointsToAnalysis pta, SootMethod rootMethod, HashMap<SootMethod, Boolean> visited) {		
		if(visited.containsKey(rootMethod))
			return;
		
		visited.put(rootMethod, true);
		
		// FIX 1: Also skip methods that do not have an active body due to exclusions (prevents crash)
		if(rootMethod.isPhantom() || !rootMethod.hasActiveBody()) return;

		if(rootMethod.getDeclaringClass().getName().startsWith("java", 0) || rootMethod.isConstructor()) return;	
		
		// iterate the CFG and get all points to information
		iterateCFG(rootMethod, pta);

		// iterate over the units in the graph
		Iterator<Edge> edges = cg.edgesOutOf(rootMethod);
		while(edges.hasNext()) {
			iterateCallGraph(cg, pta, (SootMethod) edges.next().getTgt(), visited);
		}
	}

	
	void createMethodGraph() {
		for(SootMethod sm: methodHeads.keySet()) {
			List<blockNode> heads = methodHeads.get(sm);
			
			
			HashMap<Unit, blockNode> u2b = new HashMap<Unit, blockNode>();

			ExceptionalUnitGraph g = new ExceptionalUnitGraph(sm.retrieveActiveBody());
			
			Queue<blockNode> q = new LinkedList<blockNode>();
			HashMap<Unit, Boolean> visited = new HashMap<Unit, Boolean>();

			for (blockNode bn: heads) {
				q.add(bn);
				visited.put(bn.unit, false);
				u2b.put(bn.unit, bn);
			}

			while(!q.isEmpty()) {
				blockNode bn = q.poll();
				visited.put(bn.unit, true);
				
				methodGraph.get(sm).add(bn);

				List<Unit> succs = g.getSuccsOf(bn.unit);
				for (Unit succ: succs) {
					// add the successor to the successor list of the current node
					blockNode succNode;
					
					if(u2b.containsKey(succ)) succNode = u2b.get(succ);
					else {
						succNode = new blockNode(succ, sm);
						u2b.put(succ, succNode);
					}
					
					// Deduplicate: ExceptionalUnitGraph can yield the same successor
					// on both the normal and exceptional edge; without this check the
					// Vector gets duplicate entries that inflate in/out sets later.
					if(!bn.succ.contains(succNode))
						bn.succ.add(succNode);

					// if the successor is already visited, continue
					if(visited.containsKey(succ)) continue;
					
					q.add(succNode);
					visited.put(succ, false);
				}
			}
		}
	}

	
	void simplifyMethodGraphs() {
		for(SootMethod sm: methodGraph.keySet()) {
			simplifyCFG(methodGraph.get(sm), methodHeads.get(sm));
			
			removeEmptyBlocks(methodGraph.get(sm));
		}
		
		for(SootMethod sm: methodGraph.keySet()) {
			addReturnEdges(methodGraph.get(sm));
		}
	}
	
	
	void simplifyCFG(Vector<blockNode> cfg, Vector<blockNode> heads) {
		HashMap<Unit, Boolean> visited = new HashMap<Unit, Boolean>();
		
		Queue<blockNode> q = new LinkedList<blockNode>();
		for(blockNode head: heads) {
			q.add(head);
			visited.put(head.unit, false);
		}

		while(!q.isEmpty()) {
			blockNode u = q.poll();
			visited.put(u.unit, true);

			Vector<blockNode> succsLevel1 = u.succ;

			if(succsLevel1.size() == 0) continue;
			
			int i = 0;
			while(i < succsLevel1.size()) {
				blockNode succsLevel1_i = succsLevel1.get(i);

				// if the node is a invoke statement, continue
				Boolean hasInvocation = false;
				for(ValueBox vb : ((Stmt) succsLevel1_i.unit).getUseBoxes()) {
					if(vb.getValue() instanceof InvokeExpr && !((InvokeExpr) vb.getValue()).getMethod().isConstructor()) {
						hasInvocation = true;
						break;
					}
				}
				
				if(hasInvocation) {
					// Only queue if not already fully processed – avoids repeatedly
					// resetting the visited flag and re-processing invoke nodes.
					if(!visited.containsKey(succsLevel1_i.unit) || !visited.get(succsLevel1_i.unit)) {
						q.add(succsLevel1_i);
						visited.put(succsLevel1_i.unit, false);
					}
					i++;
					continue;
				}

				Vector<blockNode> succsLevel2 = succsLevel1_i.succ;
				
				// if the successor, succsLevel1_i, of the current node, u, has only one successor, remove this intermediate successor and
				// add the second level successor to the successor list of the current node, u.
				if(succsLevel2.size()==1) {
					// Splice: replace succsLevel1_i with its sole successor in every
					// OTHER node that also pointed to succsLevel1_i.  Guard with
					// contains() so we never create duplicate succ entries.
					for(blockNode u2 : cfg) {
						if(u2.succ.contains(succsLevel1_i) && u2 != u) {
							u2.succ.remove(succsLevel1_i);
							// Only add if not already present (aliasing can make it so).
							if(!u2.succ.contains(succsLevel2.get(0)))
								u2.succ.addAll(succsLevel2);
						}
					}

					succsLevel1.remove(succsLevel1_i);
					// Guard: don't add C if it's already a direct successor of u
					// (e.g. u → [B, C] with B → [C] would create u → [C, C]).
					if(!succsLevel1.contains(succsLevel2.get(0)))
						succsLevel1.addAll(succsLevel2);

					// Only re-queue the replacement node if it hasn't been fully
					// processed yet; otherwise we'd keep resetting visited nodes.
					blockNode replacement = succsLevel2.get(0);
					if(!visited.containsKey(replacement.unit) || !visited.get(replacement.unit)) {
						visited.put(replacement.unit, false);
						q.add(replacement);
					}

					succsLevel1_i.succ.clear();
					visited.put(succsLevel1_i.unit, true);
				}
				else {
					i++;
					
					if(visited.containsKey(succsLevel1_i.unit) && visited.get(succsLevel1_i.unit)) continue;
					
					q.add(succsLevel1_i);
					visited.put(succsLevel1_i.unit, false);
				}
			}
		}
	}
	
	
	void removeEmptyBlocks(Vector<blockNode> cfg){
		Vector<blockNode> toRemove = new Vector<blockNode>();
		for(blockNode u : cfg) {
			if(!(((Stmt) u.unit) instanceof RetStmt) && !(((Stmt) u.unit) instanceof ReturnStmt) && !(((Stmt) u.unit) instanceof ReturnVoidStmt)) {
				if(u.succ.size() == 0)
					toRemove.add(u);
			}
			else {
				methodReturns.put(u.containingMethod, u);
			}
		}

		for(blockNode u: toRemove)
			cfg.remove(u);
	}
	
	
	void addReturnEdges(Vector<blockNode> cfg) {
		for(blockNode bn : cfg) {
			Boolean hasInvocation = false;
			SootMethod calledMethod = null;
			for(ValueBox vb : ((Stmt) bn.unit).getUseBoxes()) {
				if(vb.getValue() instanceof InvokeExpr && !((InvokeExpr) vb.getValue()).getMethod().isConstructor() && !((InvokeExpr) vb.getValue()).getMethod().isJavaLibraryMethod()) {
					hasInvocation = true;
					calledMethod = ((InvokeExpr) vb.getValue()).getMethod();
					break;
				}
			}
			
			if(hasInvocation) {
				// Use a set so the same return blockNode is never added twice.
				// This can happen when calledMethod appears both directly in
				// methodReturns AND as one of the overloadedMethods entries.
				LinkedHashSet<blockNode> returnNodeSet = new LinkedHashSet<blockNode>();
				
				// FIX 2: Explicitly check if the map has the method before trying to add it
				if (calledMethod != null && methodReturns.containsKey(calledMethod)) {
					returnNodeSet.add(methodReturns.get(calledMethod));
				}
				
				if(calledMethod != null && overloadedMethods.containsKey(calledMethod)) {
					for(SootMethod sm : overloadedMethods.get(calledMethod)) {
						if(methodReturns.containsKey(sm)) {
							returnNodeSet.add(methodReturns.get(sm));
						}
					}
				}
				
				for(blockNode rn : returnNodeSet) {
					// FIX 3: Safety null check before adding successor block node (avoids NullPointerException)
					if (rn != null) {
						rn.succ.add(bn);
					}
				}
			}
		}
	}
	
	
	void performContextInsensitiveAnalysis() {
		Queue<blockNode> worklist = new LinkedList<blockNode>();;
		
		for(SootMethod sm : methodGraph.keySet()) {
			for(blockNode gn : methodGraph.get(sm))
				worklist.add(gn);
		}

		Queue<blockNode> next = new LinkedList<blockNode>();

		Boolean changed = true;

		while(changed) {
			changed = false;

			while(!worklist.isEmpty()) {
				blockNode gn = worklist.poll();

				// in[n] = U out[p] for all p in pred[n]
				Stmt s = (Stmt) gn.unit;
				
				Boolean hasInvocation = false;
				SootMethod invokedMethod = null;
				for(ValueBox vb : s.getUseBoxes()) {
					if(vb.getValue() instanceof InvokeExpr && !((InvokeExpr) vb.getValue()).getMethod().isJavaLibraryMethod()) {
						hasInvocation = true;
						invokedMethod = ((InvokeExpr) vb.getValue()).getMethod();
						break;
					}
				}
				
				HashSet<Integer> in_ = new HashSet<Integer>();
				HashSet<Integer> out_ = new HashSet<Integer>();

				if(s instanceof IdentityStmt) {
					// out[n] = in[succ], in[n] = out[n] - create[method]

					for(blockNode succ : gn.succ) {
						if(succ.in != null)
							out_.addAll(succ.in);
					}

					in_.addAll(out_);
					in_.removeAll(methodCreates.get(gn.containingMethod));
				}
				else if(s instanceof ReturnStmt || s instanceof RetStmt || s instanceof ReturnVoidStmt) {
					// out[n] = U out[succ], in[n] = out[n] U uses[method]

					for(blockNode succ : gn.succ) {
						if(succ.out != null)
							out_.addAll(succ.out);
					}

					in_.addAll(out_);
					in_.addAll(methodUses.get(gn.containingMethod));
				}
				else if(hasInvocation) {
					// out[n] = in[succ], in[n] = in[entry node of its cfg]

					for(blockNode succ : gn.succ) {
						if(succ.in != null)
							out_.addAll(succ.in);
					}

					Vector<SootMethod> possibleRuntimeMethods = new Vector<SootMethod>();
					if(invokedMethod != null) possibleRuntimeMethods.add(invokedMethod);
					
					if(invokedMethod != null && overloadedMethods.containsKey(invokedMethod)) 
						possibleRuntimeMethods.addAll(overloadedMethods.get(invokedMethod));
					
					// Track whether any callee in the dispatch set is not in the call
					// graph (excluded / phantom / not analyzed by Soot).  When that
					// happens we cannot compute in_ from the callee's entry node, so
					// we must conservatively keep every heap-reachable object from the
					// call's arguments and receiver alive at this call site.
					boolean hasUnanalyzedCallee = false;

					for(SootMethod sm : possibleRuntimeMethods) {
						if(methodHeads.containsKey(sm)) {
							for(blockNode entry : methodHeads.get(sm)) {
								if(entry.in != null)
									in_.addAll(entry.in);
							}
						} else {
							// This method was excluded / is phantom / has no body –
							// it was never processed into methodHeads.
							hasUnanalyzedCallee = true;
						}
					}

					// Edge-case: invokedMethod itself is non-null but absent from
					// methodHeads (e.g. it resolves to an excluded class directly,
					// with no overloads at all).
					if (invokedMethod != null && !methodHeads.containsKey(invokedMethod))
						hasUnanalyzedCallee = true;

					// Note: Conservative handling for unanalyzed callees will be
					// implemented via FreeLink with liveness information later
				}
				else {
					// branch node, out[n] = U in[succ], in[n] = out[n]

					for(blockNode succ : gn.succ) {
						if(succ.in != null)
							out_.addAll(succ.in);
					}

					in_.addAll(out_);
				}

				if((gn.in == null) || (gn.out == null) || (gn.in != null && !in_.equals(gn.in)) || (gn.out != null && !out_.equals(gn.out))) {
					changed = true;
					gn.in = in_;
					gn.out = out_;
				}

				next.add(gn);
			}

			worklist = next;
			next = new LinkedList<blockNode>();
		}

		// methodKilled[sm] = (in[entry] U created) - in[exit]
		//
		// This is the set of objects whose lifetime is entirely contained within sm:
		//   - objects live at entry that do NOT survive to any return point
		//   - objects created inside sm
		//
		// Why in[exit] and not out[exit]?
		//
		// The backward dataflow equations at a return node are:
		//   out[return] = U out[succ]              (live in callers after the call)
		//   in[return]  = out[return] U methodUses  (adds PTS of the returned local)
		//
		// The returned value's allocation nodes are added to methodUses in
		// iterateCFG because the return statement's use-boxes contain the
		// returned local (e.g. "$r1" in "return $r1").  They therefore appear
		// in in[return] but NOT necessarily in out[return] (which only reflects
		// what specific callers were already known to need after the call).
		//
		// Subtracting out[return] fails to remove the returned object from the
		// kill set, causing freeLinks to incorrectly null fields that are part
		// of the returned value -- as seen in getCallback() where r0.callback
		// is nulled even though $r1 (= r0.callback) is returned.
		//
		// Subtracting in[return] is correct: it is the full set of objects live
		// at the return boundary, i.e. every object that must NOT be freed here.
		// Since in is a superset of out at every node, this is also strictly safer.
		for(SootMethod sm : methodGraph.keySet()) {			
			blockNode entryNode = methodHeads.get(sm).get(0);
			
			HashSet<Integer> killed = new HashSet<Integer>();

			// Start with objects live at method entry
			if (entryNode != null && entryNode.in != null) killed.addAll(entryNode.in);

			// Add objects created inside the method
			if(methodCreates.containsKey(sm))
				killed.addAll(methodCreates.get(sm));
			
			// Remove anything live just before any return point.
			// This includes the returned object (via methodUses) and anything
			// the callers need after the call (via out[return]).
			for(blockNode gn : methodGraph.get(sm)) {
				if(gn.unit instanceof ReturnStmt || gn.unit instanceof RetStmt || gn.unit instanceof ReturnVoidStmt) {
					if (gn.in != null) killed.removeAll(gn.in);
				}
			}

			methodKilled.put(sm, killed);
		}
	}

	// =========================================================================
	// ObjectLivenessResult – holds the results of object liveness analysis
	// =========================================================================
	class ObjectLivenessResult {
		HashMap<Unit, HashSet<Integer>> liveObjIn;
		HashMap<Unit, HashSet<Integer>> liveObjOut;
		
		ObjectLivenessResult(HashMap<Unit, HashSet<Integer>> in, 
		                      HashMap<Unit, HashSet<Integer>> out) {
			liveObjIn = in;
			liveObjOut = out;
		}
	}

	// =========================================================================
	// computeObjectLiveness(sm)
	//
	// Performs backward object liveness analysis on the original CFG.
	// Computes for each unit the set of objects that are live (used) from
	// that point onwards.
	//
	// Since we have flow-insensitive points-to information:
	//   LiveObjIn[n]  = UseObjSet[n] ∪ LiveObjOut[n]
	//   LiveObjOut[n] = ∪ LiveObjIn[succ] for all successors of n
	//
	// No removal of defs occurs (unlike in traditional liveness), as we
	// conservatively keep all accessed objects live.
	//
	// Handles all cases:
	//   • Direct local uses: x → PTA(x)
	//   • Field reads: x.f → PTA(x) ∪ PTA(x, f)
	//   • Field writes: x.f = y → PTA(x)  [base dereference counts as use]
	//   • Function arguments: foo(x) → PTA(x) and transitively
	//   • Return statements: return x → PTA(x)
	//   • Receiver in instance calls: x.foo() → PTA(x)
	// =========================================================================
	ObjectLivenessResult computeObjectLiveness(SootMethod sm) {
		if (!sm.hasActiveBody()) {
			return new ObjectLivenessResult(new HashMap<>(), new HashMap<>());
		}
		
		Body body = sm.getActiveBody();
		ExceptionalUnitGraph cfg = new ExceptionalUnitGraph(body);
		
		if (debug)
			System.out.println("[ObjectLiveness] Analyzing method: " + sm.getName());
		
		// ──────────────────────────────────────────────────────────────────
		// Step 1: Compute UseObjSet for each unit
		// ──────────────────────────────────────────────────────────────────
		HashMap<Unit, HashSet<Integer>> useObjSet = new HashMap<Unit, HashSet<Integer>>();
		
		for (Unit u : body.getUnits()) {
			HashSet<Integer> uses = new HashSet<Integer>();
			Stmt s = (Stmt) u;
			
			// Process use boxes: reads of variables and fields
			for (ValueBox vb : s.getUseBoxes()) {
				Value v = vb.getValue();
				
				// Case 1: Direct local use (x)
				if (v instanceof Local) {
					Local l = (Local) v;
					PointsToSet pts = pta.reachingObjects(l);
					if (!(pts instanceof EmptyPointsToSet)) {
						((DoublePointsToSet) pts).forall(new P2SetVisitor() {
							@Override
							public void visit(Node n) {
								uses.add(n.getNumber());
							}
						});
					}
				}
				// Case 2: Field read on right side (x = y.f or use of y.f)
				else if (v instanceof JInstanceFieldRef) {
					JInstanceFieldRef ref = (JInstanceFieldRef) v;
					Local base = (Local) ref.getBase();
					SootField f = (SootField) ref.getField();
					
					// Base object is used (dereferenced)
					PointsToSet basePts = pta.reachingObjects(base);
					if (!(basePts instanceof EmptyPointsToSet)) {
						((DoublePointsToSet) basePts).forall(new P2SetVisitor() {
							@Override
							public void visit(Node n) {
								uses.add(n.getNumber());
							}
						});
					}
					
					// Objects pointed to by base.f are used
					PointsToSet fieldPts = pta.reachingObjects(base, f);
					if (!(fieldPts instanceof EmptyPointsToSet)) {
						((DoublePointsToSet) fieldPts).forall(new P2SetVisitor() {
							@Override
							public void visit(Node n) {
								uses.add(n.getNumber());
							}
						});
					}
				}
			}
			
			// Process def boxes: field writes (x.f = y)
			// The base local x is used (dereferenced) even though it's in a def box
			for (ValueBox vb : s.getDefBoxes()) {
				if (vb.getValue() instanceof JInstanceFieldRef) {
					JInstanceFieldRef ref = (JInstanceFieldRef) vb.getValue();
					Local base = (Local) ref.getBase();
					
					// Base is dereferenced, so the objects it points to are used
					PointsToSet basePts = pta.reachingObjects(base);
					if (!(basePts instanceof EmptyPointsToSet)) {
						((DoublePointsToSet) basePts).forall(new P2SetVisitor() {
							@Override
							public void visit(Node n) {
								uses.add(n.getNumber());
							}
						});
					}
				}
			}
			
			// Case 3: Function calls – arguments and receiver are used
			for (ValueBox vb : s.getUseBoxes()) {
				if (vb.getValue() instanceof InvokeExpr) {
					InvokeExpr ie = (InvokeExpr) vb.getValue();
					
					// All arguments are used
					for (Value arg : ie.getArgs()) {
						if (arg instanceof Local) {
							Local l = (Local) arg;
							PointsToSet pts = pta.reachingObjects(l);
							if (!(pts instanceof EmptyPointsToSet)) {
								((DoublePointsToSet) pts).forall(new P2SetVisitor() {
									@Override
									public void visit(Node n) {
										uses.add(n.getNumber());
									}
								});
							}
						}
					}
					
					// Receiver is used for instance calls
					if (ie instanceof InstanceInvokeExpr) {
						Value receiver = ((InstanceInvokeExpr) ie).getBase();
						if (receiver instanceof Local) {
							Local l = (Local) receiver;
							PointsToSet pts = pta.reachingObjects(l);
							if (!(pts instanceof EmptyPointsToSet)) {
								((DoublePointsToSet) pts).forall(new P2SetVisitor() {
									@Override
									public void visit(Node n) {
										uses.add(n.getNumber());
									}
								});
							}
						}
					}
				}
			}
			
			// Case 4: Return statements – returned value is used
			if (s instanceof ReturnStmt) {
				ReturnStmt rs = (ReturnStmt) s;
				Value retVal = rs.getOp();
				if (retVal instanceof Local) {
					Local l = (Local) retVal;
					PointsToSet pts = pta.reachingObjects(l);
					if (!(pts instanceof EmptyPointsToSet)) {
						((DoublePointsToSet) pts).forall(new P2SetVisitor() {
							@Override
							public void visit(Node n) {
								uses.add(n.getNumber());
							}
						});
					}
				}
			}
			
			useObjSet.put(u, uses);
			
			if (debug && !uses.isEmpty())
				System.out.println("  [UseObjSet] " + u + " → " + uses);
		}
		
		// ──────────────────────────────────────────────────────────────────
		// Step 2: Backward dataflow fixpoint iteration
		// ──────────────────────────────────────────────────────────────────
		HashMap<Unit, HashSet<Integer>> liveObjIn = new HashMap<Unit, HashSet<Integer>>();
		HashMap<Unit, HashSet<Integer>> liveObjOut = new HashMap<Unit, HashSet<Integer>>();
		
		// Initialize all units with empty sets
		for (Unit u : body.getUnits()) {
			liveObjIn.put(u, new HashSet<Integer>());
			liveObjOut.put(u, new HashSet<Integer>());
		}
		
		// Fixpoint iteration: process units in reverse (backward)
		boolean changed = true;
		int iteration = 0;
		
		while (changed) {
			changed = false;
			iteration++;
			
			if (debug && iteration == 1)
				System.out.println("[ObjectLiveness] Starting fixpoint iteration...");
			
			// Process each unit in the CFG
			for (Unit u : body.getUnits()) {
				HashSet<Integer> oldIn = new HashSet<Integer>(liveObjIn.get(u));
				HashSet<Integer> oldOut = new HashSet<Integer>(liveObjOut.get(u));
				
				// Compute new LiveObjOut: union of LiveObjIn of all successors
				HashSet<Integer> newOut = new HashSet<Integer>();
				for (Unit succ : cfg.getSuccsOf(u)) {
					newOut.addAll(liveObjIn.get(succ));
				}
				
				// Compute new LiveObjIn: UseObjSet[u] ∪ LiveObjOut[u]
				// No removal of defs (flow-insensitive conservative analysis)
				HashSet<Integer> newIn = new HashSet<Integer>(useObjSet.get(u));
				newIn.addAll(newOut);
				
				liveObjIn.put(u, newIn);
				liveObjOut.put(u, newOut);
				
				// Check for convergence
				if (!oldIn.equals(newIn) || !oldOut.equals(newOut)) {
					changed = true;
				}
			}
		}
		
		if (debug)
			System.out.println("[ObjectLiveness] Converged after " + iteration + " iterations");
		
		if (debug) {
			for (Unit u : body.getUnits()) {
				System.out.println("  [In]  " + u + " → " + liveObjIn.get(u));
				System.out.println("  [Out] " + u + " → " + liveObjOut.get(u));
			}
		}
		
		return new ObjectLivenessResult(liveObjIn, liveObjOut);
	}

	

	// =========================================================================
	// Data structure for representing access paths (π)
	// =========================================================================
	class FieldPath {
		List<SootField> fields;  // ordered list of fields in the path
		Local root;               // starting local variable
		
		FieldPath(Local r) {
			root = r;
			fields = new ArrayList<SootField>();
		}
		
		FieldPath(Local r, List<SootField> f) {
			root = r;
			fields = new ArrayList<SootField>(f);
		}
		
		FieldPath append(SootField f) {
			FieldPath newPath = new FieldPath(root, fields);
			newPath.fields.add(f);
			return newPath;
		}
		
		@Override
		public String toString() {
			String s = root.getName();
			for (SootField f : fields) {
				s += "." + f.getName();
			}
			return s;
		}
	}

	// =========================================================================
	// FindFieldPaths(O, ρM, σ, σ⁻¹, LM)
	//
	// Computes access paths from local variables to a target object O and
	// extends them through field references only when the access is unambiguous.
	// The reverse map σ⁻¹ is used to ensure uniqueness.
	//
	// Returns: Set of pairs (π, O') where π is an access path and O' is the
	//          final object reached via that path.
	// =========================================================================
	Set<FieldPath> findFieldPaths(Integer O, SootMethod sm,
	                               HashSet<Local> excludedLocals,
	                               HashSet<Integer> visiting) {
		Set<FieldPath> result = new HashSet<FieldPath>();
		
		// Cycle guard
		if (visiting.contains(O)) return result;
		visiting.add(O);
		
		// Direct case: Find locals l s.t. ρM(l) = {O} and l ∉ LM
		if (object2local.containsKey(O)) {
			for (methodLocal ml : object2local.get(O)) {
				if (ml.m != sm) continue;  // belongs to another method
				if (excludedLocals.contains(ml.l)) continue;  // excluded local
				
				// Singleton check: PTA(l) must be exactly {O}
				Vector<Integer> pts = local2object.get(ml);
				if (pts != null && pts.size() == 1 && pts.get(0).equals(O)) {
					result.add(new FieldPath(ml.l));
				}
			}
		}
		
		// Indirect case: object2object2.get(O) = { fPrev → [Oprev] }
		// means Oprev.fPrev → O. Recurse to find a reachable local for Oprev.
		if (object2object2.containsKey(O)) {
			HashSet<String> triedParents = new HashSet<String>();
			for (SootField fPrev : object2object2.get(O).keySet()) {
				for (Integer Oprev : object2object2.get(O).get(fPrev)) {
					
					// Skip duplicate (Oprev, fPrev) entries
					String parentKey = Oprev + ":" + fPrev.getName();
					if (triedParents.contains(parentKey)) continue;
					triedParents.add(parentKey);
					
					// Recurse to find paths to Oprev
					Set<FieldPath> prevPaths = findFieldPaths(Oprev, sm, 
						excludedLocals, new HashSet<Integer>(visiting));
					
					for (FieldPath prevPath : prevPaths) {
						FieldPath newPath = prevPath.append(fPrev);
						
						// Check uniqueness: |σ⁻¹(Oprev, fPrev)| = 1
						// Count how many objects point to Oprev via fPrev
						int countReverse = 0;
						if (object2object2.containsKey(Oprev)) {
							if (object2object2.get(Oprev).containsKey(fPrev)) {
								countReverse = object2object2.get(Oprev).get(fPrev).size();
							}
						}
						
						if (countReverse == 1) {
							result.add(newPath);
						}
					}
				}
			}
		}
		
		visiting.remove(O);
		return result;
	}

	// =========================================================================
	// FreeLink(M, killSet, ρM, σ, σ⁻¹, LiveObjIn_M, LiveObjOut_M)
	//
	// Main freeing algorithm that processes each node in the method to free
	// objects that die at that point.
	//
	// Parameters:
	//   sm: SootMethod - the method being analyzed
	//   killSet: HashSet<Integer> - objects that die in this method
	//   liveObjIn: HashMap<Unit, HashSet<Integer>> - objects live before each unit
	//   liveObjOut: HashMap<Unit, HashSet<Integer>> - objects live after each unit
	//   excludedLocals: HashSet<Local> - safe locals (never use as path roots)
	// =========================================================================
	void freeLink(SootMethod sm, 
	              HashSet<Integer> killSet,
	              HashMap<Unit, HashSet<Integer>> liveObjIn,
	              HashMap<Unit, HashSet<Integer>> liveObjOut,
	              HashSet<Local> excludedLocals) {
		
		if (!sm.hasActiveBody()) return;
		Body body = sm.getActiveBody();
		UnitPatchingChain units = body.getUnits();
		
		if (debug)
			System.out.println("[FreeLink] Processing method: " + sm.getName());
		
		for (Unit n : units) {
			// Check if this is an exit node (return statement)
			if (n instanceof ReturnStmt || n instanceof ReturnVoidStmt || n instanceof RetStmt) {
				// At exit: free all objects in killSet
				for (Integer O : killSet) {
					freeLinkAtExit(O, sm, body, excludedLocals, n);
				}
			} else {
				// At non-exit nodes: free objects that die at this node
				// Fn = killSet ∩ (LiveObjIn[n] − LiveObjOut[n])
				HashSet<Integer> liveIn = liveObjIn.getOrDefault(n, new HashSet<Integer>());
				HashSet<Integer> liveOut = liveObjOut.getOrDefault(n, new HashSet<Integer>());
				
				HashSet<Integer> diedAtNode = new HashSet<Integer>(liveIn);
				diedAtNode.removeAll(liveOut);
				diedAtNode.retainAll(killSet);
				
				for (Integer O : diedAtNode) {
					freeLinkAtLastUse(O, sm, body, excludedLocals, n);
				}
			}
		}
	}

	// =========================================================================
	// FreeLinkAtLastUse(O, ρM, σ, σ⁻¹, LM)
	//
	// Frees field links of an object only when the target of a field access
	// is uniquely determined. For such unambiguous links, all corresponding
	// access paths are located and explicitly nulled.
	// =========================================================================
	void freeLinkAtLastUse(Integer O, SootMethod sm, Body body,
	                        HashSet<Local> excludedLocals, Unit insertionPoint) {
		
		if (!object2object2.containsKey(O)) return;
		
		for (SootField f : object2object2.get(O).keySet()) {
			for (Integer Oprime : object2object2.get(O).get(f)) {
				
				// Check uniqueness: |σ⁻¹(O', f)| = 1
				int countReverse = 1;  // We already know this is at least 1
				int countTotal = object2object2.get(O).get(f).size();
				
				// Count all objects pointing to Oprime via f
				for (Integer testO : object2object2.keySet()) {
					if (object2object2.get(testO).containsKey(f)) {
						for (Integer testDest : object2object2.get(testO).get(f)) {
							if (testDest.equals(Oprime)) countReverse++;
						}
					}
				}
				
				if (countReverse == 1) {
					Set<FieldPath> paths = findFieldPaths(O, sm, excludedLocals, 
						new HashSet<Integer>());
					
					for (FieldPath pi0 : paths) {
						FieldPath pi = pi0.append(f);
						nullPath(pi, sm, body, insertionPoint);
					}
				}
			}
		}
	}

	// =========================================================================
	// FreeLinkAtExit(O, ρM, σ, σ⁻¹, LM)
	//
	// Frees field links at method exit. Used for ambiguous links that need
	// to be freed regardless of uniqueness to prevent reference cycles.
	// =========================================================================
	void freeLinkAtExit(Integer O, SootMethod sm, Body body,
	                     HashSet<Local> excludedLocals, Unit insertionPoint) {
		
		if (!object2object2.containsKey(O)) return;
		
		for (SootField f : object2object2.get(O).keySet()) {
			for (Integer Oprime : object2object2.get(O).get(f)) {
				
				// Check uniqueness: |σ⁻¹(O', f)| > 1  (ambiguous)
				int countReverse = 0;
				for (Integer testO : object2object2.keySet()) {
					if (object2object2.get(testO).containsKey(f)) {
						for (Integer testDest : object2object2.get(testO).get(f)) {
							if (testDest.equals(Oprime)) countReverse++;
						}
					}
				}
				
				if (countReverse > 1) {
					Set<FieldPath> paths = findFieldPaths(O, sm, excludedLocals, 
						new HashSet<Integer>());
					
					for (FieldPath pi0 : paths) {
						FieldPath pi = pi0.append(f);
						nullPath(pi, sm, body, insertionPoint);
					}
				}
			}
		}
	}

	// =========================================================================
	// NULL(π)
	//
	// Emits null assignments for a field path. For intermediate fields in the
	// path, generates temporary assignments. For the final field, generates
	// the null assignment.
	//
	// Path π = ⟨l, f₁, f₂, ..., fₖ⟩
	// =========================================================================
	void nullPath(FieldPath pi, SootMethod sm, Body body, Unit insertionPoint) {
		
		if (pi.fields.isEmpty()) {
			if (debug)
				System.out.println("[NULL] Empty field path for local: " + pi.root);
			return;
		}
		
		UnitPatchingChain units = body.getUnits();
		Local curr = pi.root;
		
		for (int i = 0; i < pi.fields.size(); i++) {
			SootField fi = pi.fields.get(i);
			
			if (i == pi.fields.size() - 1) {
				// Final field: curr.fi = null
				Unit nullStmt = Jimple.v().newAssignStmt(
					Jimple.v().newInstanceFieldRef(curr, fi.makeRef()),
					NullConstant.v());
				
				units.insertBefore(nullStmt, insertionPoint);
				
				if (debug)
					System.out.println("[NULL] Inserted: " + nullStmt);
			} else {
				// Intermediate field: t = curr.fi
				Local t = Jimple.v().newLocal(
					"$freeTemp" + (tempCounter++), fi.getType());
				body.getLocals().add(t);
				
				Unit navStmt = Jimple.v().newAssignStmt(
					t,
					Jimple.v().newInstanceFieldRef(curr, fi.makeRef()));
				
				units.insertBefore(navStmt, insertionPoint);
				curr = t;
				
				if (debug)
					System.out.println("[NULL] Inserted navigation: " + navStmt);
			}
		}
	}

}