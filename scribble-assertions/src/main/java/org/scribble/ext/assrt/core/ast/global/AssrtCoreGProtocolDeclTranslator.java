package org.scribble.ext.assrt.core.ast.global;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.scribble.ast.MessageNode;
import org.scribble.ast.MessageSigNode;
import org.scribble.ast.PayloadElem;
import org.scribble.ast.UnaryPayloadElem;
import org.scribble.ast.global.GChoice;
import org.scribble.ast.global.GConnect;
import org.scribble.ast.global.GContinue;
import org.scribble.ast.global.GInteractionNode;
import org.scribble.ast.global.GProtocolBlock;
import org.scribble.ast.global.GProtocolDecl;
import org.scribble.ast.global.GProtocolDef;
import org.scribble.ast.global.GSimpleInteractionNode;
import org.scribble.ast.name.simple.RecVarNode;
import org.scribble.ast.name.simple.RoleNode;
import org.scribble.del.global.GProtocolDefDel;
import org.scribble.ext.assrt.ast.AssrtAnnotDataTypeElem;
import org.scribble.ext.assrt.ast.AssrtArithExpr;
import org.scribble.ext.assrt.ast.AssrtAssertion;
import org.scribble.ext.assrt.ast.AssrtAstFactory;
import org.scribble.ext.assrt.ast.global.AssrtGConnect;
import org.scribble.ext.assrt.ast.global.AssrtGContinue;
import org.scribble.ext.assrt.ast.global.AssrtGMessageTransfer;
import org.scribble.ext.assrt.ast.global.AssrtGRecursion;
import org.scribble.ext.assrt.ast.name.simple.AssrtIntVarNameNode;
import org.scribble.ext.assrt.core.ast.AssrtCoreActionKind;
import org.scribble.ext.assrt.core.ast.AssrtCoreAstFactory;
import org.scribble.ext.assrt.core.ast.AssrtCoreMessage;
import org.scribble.ext.assrt.core.ast.AssrtCoreSyntaxException;
import org.scribble.ext.assrt.type.formula.AssrtArithFormula;
import org.scribble.ext.assrt.type.formula.AssrtBoolFormula;
import org.scribble.ext.assrt.type.formula.AssrtTrueFormula;
import org.scribble.ext.assrt.type.name.AssrtAnnotDataType;
import org.scribble.ext.assrt.type.name.AssrtDataTypeVar;
import org.scribble.main.Job;
import org.scribble.type.kind.Global;
import org.scribble.type.kind.RecVarKind;
import org.scribble.type.name.DataType;
import org.scribble.type.name.Op;
import org.scribble.type.name.PayloadElemType;
import org.scribble.type.name.RecVar;
import org.scribble.type.name.Role;

public class AssrtCoreGProtocolDeclTranslator
{
	public static final DataType UNIT_DATATYPE = new DataType("_Unit");  // FIXME: move
	
	private final Job job;
	private final AssrtCoreAstFactory af;
	
	private static int varCounter = 1;
	private static int recCounter = 1;
	
	private static AssrtDataTypeVar makeFreshDataTypeVar()
	{
		return new AssrtDataTypeVar("_dum" + varCounter++);
	}

	private static String makeFreshRecVarName()
	{
		return "_X" + recCounter++;
	}
	
	//private static DataType UNIT_TYPE;

	public AssrtCoreGProtocolDeclTranslator(Job job, AssrtCoreAstFactory af)
	{
		this.job = job;
		this.af = af;
		
		/*if (F17GProtocolDeclTranslator.UNIT_TYPE == null)
		{
			F17GProtocolDeclTranslator.UNIT_TYPE = new DataType("_UNIT");
		}*/
	}

	public AssrtCoreGType translate(GProtocolDecl gpd) throws AssrtCoreSyntaxException
	{
		GProtocolDef inlined = ((GProtocolDefDel) gpd.def.del()).getInlinedProtocolDef();
		return parseSeq(inlined.getBlock().getInteractionSeq().getInteractions(), new HashMap<>(), false, false);
	}

	// List<GInteractionNode> because subList is useful for parsing the continuation
	private AssrtCoreGType parseSeq(List<GInteractionNode> is, Map<RecVar, RecVar> rvs,
			boolean checkChoiceGuard, boolean checkRecGuard) throws AssrtCoreSyntaxException
	{
		if (is.isEmpty())
		{
			return this.af.AssrtCoreGEnd();
		}

		GInteractionNode first = is.get(0);
		if (first instanceof GSimpleInteractionNode && !(first instanceof GContinue))
		{
			if (first instanceof AssrtGMessageTransfer)
			{
				return parseAssrtGMessageTransfer(is, rvs, (AssrtGMessageTransfer) first);
			}
			else if (first instanceof AssrtGConnect)
			{
				return parseAssrtGConnect(is, rvs, (AssrtGConnect) first);
			}
			/*else if (first instanceof GDisconnect)
			{
				F17GDisconnect gdc = parseGDisconnect((GDisconnect) first);
				AssrtCoreGType cont = parseSeq(jc, mc, is.subList(1, is.size()), false, false);
				Map<AssrtCoreGAction, AssrtCoreGType> cases = new HashMap<>();
				cases.put(gdc, cont);
				return this.factory.GChoice(cases);
			}*/
			else
			{
				throw new RuntimeException("[assrt-core] Shouldn't get in here: " + first);
			}
		}
		else
		{
			if (checkChoiceGuard)  // No "flattening" of nested choices not allowed?
			{
				throw new AssrtCoreSyntaxException(first.getSource(), "[assrt-core] Unguarded in choice case: " + first);
			}
			if (is.size() > 1)
			{
				throw new AssrtCoreSyntaxException(is.get(1).getSource(), "[assrt-core] Bad sequential composition after: " + first);
			}

			if (first instanceof GChoice)
			{
				return parseGChoice(rvs, checkRecGuard, (GChoice) first);
			}
			else if (first instanceof AssrtGRecursion)
			{
				return parseAssrtGRecursion(rvs, checkChoiceGuard, (AssrtGRecursion) first);
			}
			else if (first instanceof GContinue)
			{
				return parseAssrtGContinue(rvs, checkRecGuard, (AssrtGContinue) first);
			}
			else
			{
				throw new RuntimeException("[assrt-core] Shouldn't get in here: " + first);
			}
		}
	}

	private AssrtCoreGType parseGChoice(Map<RecVar, RecVar> rvs,
			boolean checkRecGuard, GChoice gc) throws AssrtCoreSyntaxException
	{
		List<AssrtCoreGType> children = new LinkedList<>();
		for (GProtocolBlock b : gc.getBlocks())
		{
			children.add(parseSeq(b.getInteractionSeq().getInteractions(), rvs, true, checkRecGuard));  // Check cases are guarded
		}

		Role src = null;
		Role dest = null;
		AssrtCoreActionKind<Global> kind = null;  // FIXME: generic parameter
		Map<AssrtCoreMessage, AssrtCoreGType> cases = new HashMap<>();
		for (AssrtCoreGType c : children)
		{
			// Because all cases should be action guards (unary choices)
			if (!(c instanceof AssrtCoreGChoice))
			{
				throw new RuntimeException("[assrt-core] Shouldn't get in here: " + c);
			}
			AssrtCoreGChoice tmp = (AssrtCoreGChoice) c;
			if (tmp.cases.size() > 1)
			{
				throw new RuntimeException("[assrt-core] Shouldn't get in here: " + c);
			}
			
			if (kind == null)
			{
				kind = tmp.kind;
				src = tmp.src;
				dest = tmp.dest;
			}
			else if (!kind.equals(tmp.kind))
			{
				throw new AssrtCoreSyntaxException(gc.getSource(), "[assrt-core] Mixed-action choices not supported: " + gc);
			}
			else if (!src.equals(tmp.src) || !dest.equals(tmp.dest))
			{
				throw new AssrtCoreSyntaxException(gc.getSource(), "[assrt-core] Non-directed choice not supported: " + gc);
			}
			
			// "Flatten" nested choices (already checked they are guarded) -- Scribble choice subjects ignored
			for (Entry<AssrtCoreMessage, AssrtCoreGType> e : tmp.cases.entrySet())
			{
				AssrtCoreMessage k = e.getKey();
				if (cases.keySet().stream().anyMatch(x -> x.op.equals(k.op)))
				{
					throw new AssrtCoreSyntaxException(gc.getSource(), "[assrt-core] Non-deterministic actions not supported: " + k.op);
				}
				cases.put(k, e.getValue());
			}
		}
		
		return this.af.AssrtCoreGChoice(src, (AssrtCoreGActionKind) kind, dest, cases);
	}

	private AssrtCoreGType parseAssrtGRecursion(Map<RecVar, RecVar> rvs,
			boolean checkChoiceGuard, AssrtGRecursion gr) throws AssrtCoreSyntaxException
	{
		RecVar recvar = gr.recvar.toName();
		if (recvar.toString().contains("__"))  // HACK: "inlined proto rec var"
		{
			RecVarNode rvn = (RecVarNode) ((AssrtAstFactory) this.job.af).SimpleNameNode(null, RecVarKind.KIND, makeFreshRecVarName());
			rvs.put(recvar, rvn.toName());
			recvar = rvn.toName();
		}
		AssrtCoreGType body = parseSeq(gr.getBlock().getInteractionSeq().getInteractions(), rvs, checkChoiceGuard, true);  // Check rec body is guarded

		//return this.af.AssrtCoreGRec(recvar, annot, init, body);
		//return this.af.AssrtCoreGRec(recvar, Stream.of(annot).collect(Collectors.toMap(a -> a, a -> init)), body);
		Iterator<AssrtArithExpr> exprs = gr.annotexprs.iterator();
		/*Map<AssrtDataTypeVar, AssrtArithFormula> vars
				= gr.annotvars.stream().collect(Collectors.toMap(v -> v.getFormula().toName(), v -> exprs.next().getFormula()));*/
		LinkedHashMap<AssrtDataTypeVar, AssrtArithFormula> vars = new LinkedHashMap<>();
		for (AssrtIntVarNameNode vv : gr.annotvars)
		{
			vars.put(vv.getFormula().toName(), exprs.next().getFormula());
		}
		AssrtBoolFormula ass = (gr.ass == null) ? AssrtTrueFormula.TRUE : gr.ass.getFormula();
		return this.af.AssrtCoreGRec(recvar, vars, body, ass);
	}

	private AssrtCoreGType parseAssrtGContinue(Map<RecVar, RecVar> rvs, boolean checkRecGuard, AssrtGContinue gc)
			throws AssrtCoreSyntaxException
	{
		if (checkRecGuard)
		{
			throw new AssrtCoreSyntaxException(gc.getSource(), "[assrt-core] Unguarded in recursion: " + gc);  // FIXME: too conservative, e.g., rec X . A -> B . rec Y . X
		}
		RecVar recvar = gc.recvar.toName();
		if (rvs.containsKey(recvar))
		{
			recvar = rvs.get(recvar);
		}
		List<AssrtArithFormula> exprs = gc.annotexprs.stream().map(e -> e.getFormula()).collect(Collectors.toList());
		return this.af.AssrtCoreGRecVar(recvar, exprs);
	}

	// Parses message interactions as unary choices
	private AssrtCoreGChoice parseAssrtGMessageTransfer(List<GInteractionNode> is, Map<RecVar, RecVar> rvs, AssrtGMessageTransfer gmt) throws AssrtCoreSyntaxException 
	{
		Op op = parseOp(gmt);
		//AssrtAnnotDataType pay = parsePayload(gmt);
		List<AssrtAnnotDataType> pays = parsePayload(gmt);
		AssrtAssertion ass = parseAssertion(gmt);
		AssrtCoreMessage a = this.af.AssrtCoreAction(op, pays, ass.getFormula());
		Role src = parseSourceRole(gmt);
		Role dest = parseDestinationRole(gmt);
		AssrtCoreGActionKind kind = AssrtCoreGActionKind.MESSAGE;
		return parseGSimpleInteractionNode(is, rvs, src, a, dest, kind);
	}

	// Duplicated from parseGMessageTransfer (MessageTransfer and ConnectionAction have no common base
	
	private AssrtCoreGChoice parseAssrtGConnect(List<GInteractionNode> is, Map<RecVar, RecVar> rvs, AssrtGConnect gc) throws AssrtCoreSyntaxException 
	{
		Op op = parseOp(gc);
		//AssrtAnnotDataType pay = parsePayload(gc);
		List<AssrtAnnotDataType> pays = parsePayload(gc);
		AssrtAssertion ass = parseAssertion(gc);
		AssrtCoreMessage a = this.af.AssrtCoreAction(op, pays, ass.getFormula());
		Role src = parseSourceRole(gc);
		Role dest = parseDestinationRole(gc);
		AssrtCoreGActionKind kind = AssrtCoreGActionKind.CONNECT;
		return parseGSimpleInteractionNode(is, rvs, src, a, dest, kind);
	}

	private AssrtCoreGChoice parseGSimpleInteractionNode(
			List<GInteractionNode> is, Map<RecVar, RecVar> rvs, 
			Role src, AssrtCoreMessage a, Role dest, AssrtCoreGActionKind kind) throws AssrtCoreSyntaxException 
	{
		if (src.equals(dest))
		{
			throw new RuntimeException("[assrt-core] Shouldn't get in here (self-communication): " + src + ", " + dest);
		}
		
		AssrtCoreGType cont = parseSeq(is.subList(1, is.size()), rvs, false, false);  // Subseqeuent choice/rec is guarded by (at least) this action
		return this.af.AssrtCoreGChoice(src, kind, dest, Stream.of(a).collect(Collectors.toMap(x -> x, x -> cont)));
	}

	private Op parseOp(AssrtGMessageTransfer gmt) throws AssrtCoreSyntaxException
	{
		return parseOp(gmt.msg);
	}

	private Op parseOp(AssrtGConnect gc) throws AssrtCoreSyntaxException
	{
		return parseOp(gc.msg);
	}

	private Op parseOp(MessageNode mn) throws AssrtCoreSyntaxException
	{
		if (!mn.isMessageSigNode())
		{
			throw new AssrtCoreSyntaxException(mn.getSource(), " [assrt-core] Message sig names not supported: " + mn);  // TODO: MessageSigName
		}
		MessageSigNode msn = ((MessageSigNode) mn);
		return msn.op.toName();
	}

	//private AssrtAnnotDataType parsePayload(AssrtGMessageTransfer gmt) throws AssrtCoreSyntaxException
	private List<AssrtAnnotDataType> parsePayload(AssrtGMessageTransfer gmt) throws AssrtCoreSyntaxException
	{
		return parsePayload(gmt.msg);
	}

	//private AssrtAnnotDataType parsePayload(AssrtGConnect gc) throws AssrtCoreSyntaxException
	private List<AssrtAnnotDataType> parsePayload(AssrtGConnect gc) throws AssrtCoreSyntaxException
	{
		return parsePayload(gc.msg);
	}

	//private AssrtAnnotDataType parsePayload(MessageNode mn) throws AssrtCoreSyntaxException
	private List<AssrtAnnotDataType> parsePayload(MessageNode mn) throws AssrtCoreSyntaxException
	{
		if (!mn.isMessageSigNode())
		{
			throw new AssrtCoreSyntaxException(mn.getSource(), " [assrt-core] Message sig names not supported: " + mn);  // TODO: MessageSigName
		}
		MessageSigNode msn = ((MessageSigNode) mn);
		if (msn.payloads.getElements().isEmpty())
		{
			/*DataTypeNode dtn = (DataTypeNode) ((AssrtAstFactory) this.job.af).QualifiedNameNode(null, DataTypeKind.KIND, "_Unit");
			AssrtVarNameNode nn = (AssrtVarNameNode) ((AssrtAstFactory) this.job.af).SimpleNameNode(null, AssrtVarNameKind.KIND, "_x" + nextVarIndex());
			return ((AssrtAstFactory) this.job.af).AssrtAnnotPayloadElem(null, nn, dtn);  // null source OK?*/

			return Stream.of(new AssrtAnnotDataType(makeFreshDataTypeVar(), AssrtCoreGProtocolDeclTranslator.UNIT_DATATYPE))
					.collect(Collectors.toList());  // FIXME: make empty list
		}
		/*else if (msn.payloads.getElements().size() > 1)
		{
			throw new AssrtCoreSyntaxException(msn.getSource(), "[assrt-core] Payload with more than one element not supported: " + mn);
		}*/

		//PayloadElem<?> pe = msn.payloads.getElements().get(0);
		List<AssrtAnnotDataType> res = new LinkedList<>();
		for (PayloadElem<?> pe : msn.payloads.getElements())
		{
			if (!(pe instanceof AssrtAnnotDataTypeElem) && !(pe instanceof UnaryPayloadElem<?>))
			{
				// Already ruled out by parsing?  e.g., GDelegationElem
				throw new AssrtCoreSyntaxException("[assrt-core] Payload element not supported: " + pe);
			}
			/*else if (pe instanceof LDelegationElem)  // No: only created by projection, won't be parsed
			{
				throw new AssrtCoreSyntaxException("[assrt-core] Payload element not supported: " + pe);
			}*/
			
			if (pe instanceof AssrtAnnotDataTypeElem)
			{
				AssrtAnnotDataType adt = ((AssrtAnnotDataTypeElem) pe).toPayloadType();
				String type = adt.data.toString();
				if (!type.equals("int") && !type.endsWith(".int"))  // HACK FIXME (currently "int" for F#)
				{
					throw new AssrtCoreSyntaxException(pe.getSource(), "[assrt-core] Payload annotations not supported for non- \"int\" type kind: " + pe);
				}
				
				// FIXME: non-annotated payload elems get created with fresh vars, i.e., non- int types
				// Also empty payloads are created as Unit type
				// But current model building implicitly treats all vars as int -- this works, but is not clean
				
				//return adt;
				res.add(adt);
			}
			else
			{
				PayloadElemType<?> pet = ((UnaryPayloadElem<?>) pe).toPayloadType();
				if (!pet.isDataType())
				{
				// i.e., AssrtDataTypeVar not allowed (should be "encoded")
					throw new AssrtCoreSyntaxException(pe.getSource(), "[assrt-core] Non- datatype kind payload not supported: " + pe);
				}
				//return new AssrtAnnotDataType(makeFreshDataTypeVar(), (DataType) pet);
				res.add(new AssrtAnnotDataType(makeFreshDataTypeVar(), (DataType) pet));
			}
		}
		return res;
	}

	private AssrtAssertion parseAssertion(AssrtGMessageTransfer gmt)
	{
		return parseAssertion(gmt.ass);
	}

	private AssrtAssertion parseAssertion(AssrtGConnect gc)
	{
		return parseAssertion(gc.ass);
	}

	// Empty assertions generated as True
	private AssrtAssertion parseAssertion(AssrtAssertion ass)
	{
		return (ass == null) ? ((AssrtAstFactory) this.job.af).AssrtAssertion(null, AssrtTrueFormula.TRUE) : ass;
			// FIXME: singleton constant
	}

	private Role parseSourceRole(AssrtGMessageTransfer gmt)
	{
		return parseSourceRole(gmt.src);
	}

	private Role parseSourceRole(GConnect gmt)
	{
		return parseSourceRole(gmt.src);
	}

	private Role parseSourceRole(RoleNode rn)
	{
		return rn.toName();
	}
	
	private Role parseDestinationRole(AssrtGMessageTransfer gmt) throws AssrtCoreSyntaxException
	{
		if (gmt.getDestinations().size() > 1)
		{
			throw new AssrtCoreSyntaxException(gmt.getSource(), " [TODO] Multicast not supported: " + gmt);
		}
		return parseDestinationRole(gmt.getDestinations().get(0));
	}

	private Role parseDestinationRole(AssrtGConnect gc) throws AssrtCoreSyntaxException
	{
		return parseDestinationRole(gc.dest);
	}

	private Role parseDestinationRole(RoleNode rn) throws AssrtCoreSyntaxException
	{
		return rn.toName();
	}

	
	
	
	
	
	
	
	
	
	/*
	// Mostly duplicated from parseGMessageTransfer, but GMessageTransfer/GConnect have no useful base class 
	private AssrtCoreGConnect parseGConnect(GConnect gc) throws F17Exception 
	{
		Role src = gc.src.toName();
		Role dest = gc.dest.toName();
		if (!gc.msg.isMessageSigNode())
		{
			throw new F17SyntaxException(gc.msg.getSource(), " [f17] Message kind not supported: " + gc.msg);
		}
		MessageSigNode msn = ((MessageSigNode) gc.msg);
		Op op = msn.op.toName();
		Payload pay = null;
		if (msn.payloads.getElements().isEmpty())
		{
			pay = Payload.EMPTY_PAYLOAD;
		}
		else
		{
			String tmp = msn.payloads.getElements().get(0).toString().trim();
			int i = tmp.indexOf('@');
			if (i != -1)
			{
				throw new F17Exception("[f17] Delegation not supported: " + tmp);
			}
			else
			{
				pay = msn.payloads.toPayload();
			}
		}
		return this.factory.GConnect(src, dest, op, pay);
	}
	*/
	
	/*private AssrtCoreGType parseSeq(JobContext jc, ModuleContext mc, List<GInteractionNode> is,
			boolean checkChoiceGuard, boolean checkRecGuard) throws F17Exception
	{
		//List<GInteractionNode> is = block.getInteractionSeq().getInteractions();
		if (is.isEmpty())
		{
			return this.factory.GEnd();
		}

		GInteractionNode first = is.get(0);
		if (first instanceof GSimpleInteractionNode && !(first instanceof GContinue))
		{
			if (first instanceof GMessageTransfer)
			{
				AssrtCoreGMessageTransfer gmt = parseGMessageTransfer((GMessageTransfer) first);
				AssrtCoreGType cont = parseSeq(jc, mc, is.subList(1, is.size()), false, false);
				Map<AssrtCoreGAction, AssrtCoreGType> cases = new HashMap<>();
					cases.put(gmt, cont);
				return this.factory.GChoice(cases);
			}
			else if (first instanceof GConnect)
			{
				AssrtCoreGConnect gc = parseGConnect((GConnect) first);
				AssrtCoreGType cont = parseSeq(jc, mc, is.subList(1, is.size()), false, false);
				Map<AssrtCoreGAction, AssrtCoreGType> cases = new HashMap<>();
				cases.put(gc, cont);
				return this.factory.GChoice(cases);
			}
			else if (first instanceof GDisconnect)
			{
				F17GDisconnect gdc = parseGDisconnect((GDisconnect) first);
				AssrtCoreGType cont = parseSeq(jc, mc, is.subList(1, is.size()), false, false);
				Map<AssrtCoreGAction, AssrtCoreGType> cases = new HashMap<>();
				cases.put(gdc, cont);
				return this.factory.GChoice(cases);
			}
			else
			{
				throw new RuntimeException("[f17] Shouldn't get in here: " + first);
			}
		}
		else
		{
			if (checkChoiceGuard)
			{
				throw new F17SyntaxException(first.getSource(), "[f17] Unguarded in choice case: " + first);
			}
			if (is.size() > 1)
			{
				throw new F17SyntaxException(is.get(1).getSource(), "[f17] Bad sequential composition after: " + first);
			}

			if (first instanceof GChoice)
			{
				/*if (checkRecGuard)
				{
					throw new F17Exception(first.getSource(), "[f17] Unguarded in choice case (2): " + first);
				}* /

				GChoice gc = (GChoice) first; 
				List<AssrtCoreGType> parsed = new LinkedList<>();
				for (GProtocolBlock b : gc.getBlocks())
				{
					parsed.add(parseSeq(jc, mc, b.getInteractionSeq().getInteractions(), true, checkRecGuard));  // "Directly" nested choice will still return a GlobalSend (which is really a choice; uniform global choice constructor is convenient)
				}
				Map<AssrtCoreGAction, AssrtCoreGType> cases = new HashMap<>();
				for (AssrtCoreGType p : parsed)
				{
					if (!(p instanceof AssrtCoreGChoice))
					{
						throw new RuntimeException("[f17] Shouldn't get in here: " + p);
					}
					AssrtCoreGChoice tmp = (AssrtCoreGChoice) p;
					//tmp.cases.entrySet().forEach((e) -> cases.put(e.getKey(), e.getValue()));
					for (Entry<AssrtCoreGAction, AssrtCoreGType> e : tmp.cases.entrySet())
					{
						AssrtCoreGAction k = e.getKey();
						if (k.isMessageAction())
						{
							if (cases.keySet().stream().anyMatch((x) ->
									x.isMessageAction() && ((F17MessageAction) k).getOp().equals(((F17MessageAction) x).getOp())))
							{
								throw new F17SyntaxException("[f17] Non-determinism (" + e.getKey() + ") not supported: " + gc);
							}
						}
						cases.put(k, e.getValue());
					}
				}
				return this.factory.GChoice(cases);
			}
			else if (first instanceof GRecursion)
			{
				GRecursion gr = (GRecursion) first;
				RecVar recvar = gr.recvar.toName();
				AssrtCoreGType body = parseSeq(jc, mc, gr.getBlock().getInteractionSeq().getInteractions(), checkChoiceGuard, true);
				return new AssrtCoreGRec(recvar, body);
			}
			else if (first instanceof GContinue)
			{
				if (checkRecGuard)
				{
					throw new F17SyntaxException(first.getSource(), "[f17] Unguarded in recursion: " + first);  // FIXME: conservative, e.g., rec X . A -> B . rec Y . X
				}

				return this.factory.GRecVar(((GContinue) first).recvar.toName());
			}
			else
			{
				throw new RuntimeException("[f17] Shouldn't get in here: " + first);
			}
		}
	}

	private AssrtCoreGMessageTransfer parseGMessageTransfer(GMessageTransfer gmt) throws F17Exception 
	{
		Role src = gmt.src.toName();
		if (gmt.getDestinations().size() > 1)
		{
			throw new F17Exception(gmt.getSource(), " [TODO] Multicast not supported: " + gmt);
		}
		Role dest = gmt.getDestinations().get(0).toName();
		if (!gmt.msg.isMessageSigNode())
		{
			throw new F17SyntaxException(gmt.msg.getSource(), " [f17] Not supported: " + gmt.msg);  // TODO: MessageSigName
		}
		MessageSigNode msn = ((MessageSigNode) gmt.msg);
		Op op = msn.op.toName();
		Payload pay = null;
		if (msn.payloads.getElements().isEmpty())
		{
			pay = Payload.EMPTY_PAYLOAD;
		}
		else
		{
			String tmp = msn.payloads.getElements().get(0).toString().trim();
			int i = tmp.indexOf('@');
			if (i != -1)
			{
				throw new F17Exception("[f17] Delegation not supported: " + tmp);
			}
			else
			{
				pay = msn.payloads.toPayload();
			}
		}
		return this.factory.GMessageTransfer(src, dest, op, pay);
	}

	// Mostly duplicated from parseGMessageTransfer, but GMessageTransfer/GConnect have no useful base class 
	private AssrtCoreGConnect parseGConnect(GConnect gc) throws F17Exception 
	{
		Role src = gc.src.toName();
		Role dest = gc.dest.toName();
		if (!gc.msg.isMessageSigNode())
		{
			throw new F17SyntaxException(gc.msg.getSource(), " [f17] Message kind not supported: " + gc.msg);
		}
		MessageSigNode msn = ((MessageSigNode) gc.msg);
		Op op = msn.op.toName();
		Payload pay = null;
		if (msn.payloads.getElements().isEmpty())
		{
			pay = Payload.EMPTY_PAYLOAD;
		}
		else
		{
			String tmp = msn.payloads.getElements().get(0).toString().trim();
			int i = tmp.indexOf('@');
			if (i != -1)
			{
				throw new F17Exception("[f17] Delegation not supported: " + tmp);
			}
			else
			{
				pay = msn.payloads.toPayload();
			}
		}
		return this.factory.GConnect(src, dest, op, pay);
	}

	private F17GDisconnect parseGDisconnect(GDisconnect gdc) throws F17Exception 
	{
		Role src = gdc.src.toName();
		Role dest = gdc.dest.toName();
		return this.factory.GDisconnect(src, dest);
	}*/
}