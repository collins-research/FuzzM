package jfuzz.engines;

import java.util.List;
import java.util.Map;

import jfuzz.JFuzzConfiguration;
import jfuzz.engines.messages.CounterExampleMessage;
import jfuzz.engines.messages.ExitException;
import jfuzz.engines.messages.FeatureID;
import jfuzz.engines.messages.GeneralizedMessage;
import jfuzz.engines.messages.IntervalVectorMessage;
import jfuzz.engines.messages.QueueName;
import jfuzz.engines.messages.ReceiveQueue;
import jfuzz.engines.messages.TestVectorMessage;
import jfuzz.engines.messages.TransmitQueue;
import jfuzz.lustre.BooleanCtx;
import jfuzz.lustre.FuzzProgram;
import jfuzz.lustre.generalize.PolygonalGeneralizer;
import jfuzz.poly.PolyBool;
import jfuzz.poly.RegionBounds;
import jfuzz.util.Debug;
import jfuzz.util.EvaluatableSignal;
import jfuzz.util.ID;
import jfuzz.util.IntervalVector;
import jfuzz.util.JFuzzInterval;
import jfuzz.util.JFuzzName;
import jfuzz.util.TypedName;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.NamedType;
import jkind.lustre.Program;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;

/**
 * The Generalization engine takes counter examples from the
 * solver and generalizes them.
 *
 * @param <SModel>
 */
public class GeneralizationEngine extends Engine {

	final ReceiveQueue<CounterExampleMessage>  cequeue;
	final TransmitQueue<GeneralizedMessage>    genserver;
	final TransmitQueue<IntervalVectorMessage> intserver;
	//List<VarDecl> inputNames;
//	private static final SimulationResults TRUE = new ConcreteSimulationResults();

	public GeneralizationEngine(JFuzzConfiguration cfg, Director director) {
		super(EngineName.GeneralizationEngine, cfg, director);
		cequeue = new ReceiveQueue<CounterExampleMessage>(0,this);

		genserver = new TransmitQueue<GeneralizedMessage>(this,QueueName.GeneralizedMessage);
		intserver = new TransmitQueue<IntervalVectorMessage>(this,QueueName.IntervalVectorMessage);
		this.tx.add(genserver);
		this.tx.add(intserver);
	}
	
	@Override
	protected void handleMessage(CounterExampleMessage m) {
		cequeue.push(m);
	}
	
	@Override
	protected void handleMessage(TestVectorMessage m) {
		assert(false);
	}	

	@SuppressWarnings("unused")
	private BooleanCtx packageAssertions (){
		List<Expr> assertions = model.getMainNode().assertions;
		BooleanCtx assertionCtx = new BooleanCtx(assertions);

		assertionCtx.bind(JFuzzName.assertion);
		Expr andedExpr = assertionCtx.getExpr();
		
		Expr assertExpr = new IdExpr(JFuzzName.assertion);
		Expr preassert  = new UnaryExpr(UnaryOp.PRE, assertExpr);

		Expr arrowRHS     = new BinaryExpr(preassert, BinaryOp.AND, andedExpr);
		Expr assertionRHS = new BinaryExpr(andedExpr, BinaryOp.ARROW, arrowRHS);

		assertExpr = assertionCtx.define(JFuzzName.assertion, NamedType.BOOL, assertionRHS);
		assertionCtx.setExpr(assertExpr);
		return assertionCtx;
	}
	
	GeneralizedMessage generalizeCounterExample(CounterExampleMessage m) {
		// For now we just generalize.
		// TODO: we eventually want to target a vector.
		int k = m.counterExample.size();
		assert(k > 0);

		
		//System.out.println(ID.location() + m);
		Program testMain = FuzzProgram.fuzz(model,m.prop);
		//System.out.println(ID.location() + "\n" + testMain);
		
		EvaluatableSignal evaluatableCEX = m.counterExample.evaluatableSignal();
		
		// Polygonal generalization ..

		System.out.println(ID.location() + "Starting Generalization ..");
		PolyBool polyCEX = PolygonalGeneralizer.generalizeInterface(evaluatableCEX,JFuzzName.fuzzProperty,m.fns,testMain).result;
		if (Debug.isEnabled()) {
			System.out.println(ID.location() + "Generalization : " + polyCEX);
			//System.out.println(ID.location() + "ACL2 : " + polyCEX.toACL2());
		}

		// Event-based generalization ..
//		
// 		Simulator genSim = Simulator.newSimulator(evaluatableCEX,m.fns, JFuzzName.fuzzProperty, testMain, TRUE);
//		Generalizer generalizer = new Generalizer(genSim);
//		
//		List<SignalName> signalNames = m.counterExample.signalNames();
//		Collections.shuffle(signalNames);
//		Map<SignalName,EvaluatableValue> genMap = generalizer.eventBasedGeneralization(signalNames);
		
//		IntervalSignal res = new IntervalSignal();
//		for (int time=0;time<m.counterExample.size();time++) {
//			IntervalVector iv = new IntervalVector();
//			RatVect cv = m.counterExample.get(time);
//			for (TypedName name : cv.keySet()) {
//				SignalName sn = new SignalName(name,time);
//				EvaluatableValue itz = genMap.get(sn);
//				JFuzzInterval bkz = boundInterval(itz,cfg.getSpan().get(name));
//				iv.put(name, bkz);
//			}	
//			res.add(iv);
//		}
		
		/*
		JFuzzModel cex = new JFuzzModel(testMain.getMainNode(),m.counterExample); 
		SimpleModel sm = cex.toSimpleModel();
		Specification specification = new Specification(testMain.getMainNode(),testMain.functions,true,false);
		// Modifies sm ..
		try {
			ModelReconstructionEvaluator.reconstruct(specification, sm, JFuzzName.fuzzProperty, k, true);
			ModelGeneralizer mg = new ModelGeneralizer(specification,JFuzzName.fuzzProperty,sm,k);
			//List<StreamIndex> z = m.signal.encode().keySet().stream().map(x -> StreamIndex.decode(x)).collect(Collectors.toList());
			//Collections.shuffle(z);
			//List<StreamIndex> streamIndices = new ArrayList<>();
			//for (SignalName sn: signalNames) {
			//    streamIndices.add(new StreamIndex(sn.name,sn.time));
			//}
			Model gem;
			{
				long startTime = System.currentTimeMillis();
				gem = mg.generalize();
				long endTime = System.currentTimeMillis();
				System.out.println(ID.location() + "JKind Generalization Time = " + (endTime - startTime) + " ms");
			}
			res = new IntervalSignal(k, testMain.getMainNode().inputs, gem, cfg.getSpan());
			for (int time=0;time<res.size();time++) {
				IntervalVector iv = res.get(time);
				for (String name : iv.keySet()) {
					SignalName sn = new SignalName(name,time);
					//EvaluatableValue itz = genMap.get(sn);
					JFuzzInterval bkz = iv.get(name);
					//System.out.println(ID.location() + "Generalized Value " + sn + " : " + bkz); // + " ~=~ "+ itz);
					//assert(itz.getLow().equals(bkz.min));
					//assert(itz.getHigh().equals(bkz.max));
				}
			}

		} catch (Throwable t) {
			System.out.println(ID.location() + "JKind Generalization Failed : " + m);
			System.out.flush();
			throw new Error(t);
		}
		*/
		
		if(m.id.constraintID == -1){
			// here the span holds its default values		  
			initSpan(polyCEX.intervalBounds(), m.id);
			// now the span holds the (possibly new) actual input bounds(from vacuous constraint)
		}		
		return new GeneralizedMessage(name,m,polyCEX);
	}

//	private JFuzzInterval boundInterval(EvaluatableValue itz, JFuzzInterval jFuzzInterval) {
//		InstanceType<?> max = ((EvaluatableType<?>) itz).getHigh();
//		InstanceType<?> min = ((EvaluatableType<?>) itz).getLow();
//		BigFraction bmax = max.isFinite() ? ((RationalValue) max.rationalType()).value() : jFuzzInterval.max;
//		BigFraction bmin = min.isFinite() ? ((RationalValue) min.rationalType()).value() : jFuzzInterval.min;
//		return new JFuzzInterval(jFuzzInterval.type,bmin,bmax);
//	}

	private void initSpan (Map<TypedName,RegionBounds> zed, FeatureID cid) {
		IntervalVector newSpan = new IntervalVector(cfg.getSpan());
		for (TypedName name: zed.keySet()) {
			if (newSpan.containsKey(name)) {
				JFuzzInterval iv = newSpan.get(name);
				RegionBounds  bnd = zed.get(name);
				newSpan.put(name, bnd.updateInterval(iv));
			}
		}
		cfg.setSpan(newSpan);
		System.out.println(ID.location() + "Updated Span : " + newSpan);
		// TODO: delete the following line
		// intserver.push(new IntervalVectorMessage(name,cid));
	}

	@Override
	protected void main() {
		System.out.println(ID.location() + name + " is starting ..");
		try {
			while (true) {
				CounterExampleMessage cem = cequeue.pop();
				GeneralizedMessage res = generalizeCounterExample(cem);
				genserver.push(res);
			}
		} catch (ExitException e) {

		}
		System.out.println(ID.location() + name + " is exiting.");
	}

}
