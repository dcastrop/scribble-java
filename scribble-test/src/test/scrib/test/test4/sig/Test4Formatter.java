package test.test4.sig;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;

import org.scribble.runtime.net.ScribMessage;
import org.scribble.runtime.net.ScribMessageFormatter;

public class Test4Formatter implements ScribMessageFormatter
{
	public static Charset cs = Charset.forName("UTF8");

	public Test4Formatter()
	{

	}

	@Override
	public byte[] toBytes(ScribMessage m) throws IOException
	{
		return ((Test4Message) m).toBytes();
	}

	@Override
	public ScribMessage fromBytes(ByteBuffer bb) throws IOException, ClassNotFoundException
	{
		bb.flip();
		int rem = bb.remaining();
		if (rem < 3)
		{
			bb.compact();
			return null;
		}

		int pos = bb.position();
		String m = new String(new byte[] { bb.get(pos), bb.get(pos + 1), bb.get(pos + 2) }, Test4Formatter.cs);
		switch (m)
		{
			case "Foo":
			{
				String body = readLine(bb, pos + 3).trim();  // Whitespace already built into the message classes
				bb.compact();
				if (body == null)
				{
					return null;
				}
				return new Foo(body);
			}
			case "Bar":
			{
				String body = readLine(bb, pos + 3).trim();  // Whitespace already built into the message classes
				bb.compact();
				if (body == null)
				{
					return null;
				}
				return new Bar(Integer.parseInt(body));
			}
			default: throw new RuntimeException("Deserialization error: " + m);
		}
	}
	
	private static String readLine(ByteBuffer bb, int i) throws IOException
	{
		StringBuilder sb = new StringBuilder();
		for (int limit = bb.limit(); i <= limit; )
		{
			char c = (char) bb.get(i++);
			sb.append(c);
			if (c == '\n')
			{
				bb.position(i);
				return sb.substring(0, sb.length() - 1).toString();	
			}
		}
		return null;
	}
	
	/*// Duplicated from HttpMessageFormatter  // FIXME: factor out
	private int isStatusCode(String front)
	{
		String code = "";
		for (int i = 0; i < 4; i++)
		{
			//char c = (char) bs[i];
			char c = front.charAt(i);
			if (i < 3)
			{
				if (c < '0' || c > '9')
				{
					return -1;
				}
				code += c;
			}
			else
			{
				if (c != ' ' && c != '-')  // HACK: hypen
				{
					return -1;
				}
			}
		}
		return Integer.parseInt(code);
	}*/
	

	@Override
	public void writeMessage(DataOutputStream dos, ScribMessage m) throws IOException
	{
		throw new RuntimeException("Deprecated: " + m);
	}

	@Override
	public Test4Message readMessage(DataInputStream dis) throws IOException
	{
		throw new RuntimeException("Deprecated: ");
	}
}
