//$ java -cp modules/cli/target/classes/';'modules/core/target/classes';'modules/demos/target/classes smtp.SmtpC


package smtp;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Base64;

import org.scribble.net.Buf;
import org.scribble.net.session.SSLSocketChannelWrapper;
import org.scribble.net.session.MPSTEndpoint;
import org.scribble.net.session.SocketChannelEndpoint;

import smtp.Smtp.Smtp.Smtp;
import smtp.Smtp.Smtp.channels.C.Smtp_C_1;
import smtp.Smtp.Smtp.channels.C.Smtp_C_10;
import smtp.Smtp.Smtp.channels.C.Smtp_C_11_Cases;
import smtp.Smtp.Smtp.channels.C.Smtp_C_12;
import smtp.Smtp.Smtp.channels.C.Smtp_C_2;
import smtp.Smtp.Smtp.channels.C.Smtp_C_3;
import smtp.Smtp.Smtp.channels.C.Smtp_C_3_Cases;
import smtp.Smtp.Smtp.channels.C.Smtp_C_4;
import smtp.Smtp.Smtp.channels.C.Smtp_C_6;
import smtp.Smtp.Smtp.channels.C.Smtp_C_7;
import smtp.Smtp.Smtp.channels.C.Smtp_C_7_Cases;
import smtp.Smtp.Smtp.channels.C.Smtp_C_8;
import smtp.Smtp.Smtp.channels.C.Smtp_C_9_Cases;
import smtp.Smtp.Smtp.roles.C;
import smtp.message.SmtpMessageFormatter;
import smtp.message.client.Auth;
import smtp.message.client.Data;
import smtp.message.client.DataLine;
import smtp.message.client.Ehlo;
import smtp.message.client.EndOfData;
import smtp.message.client.Mail;
import smtp.message.client.Quit;
import smtp.message.client.Rcpt;
import smtp.message.client.StartTls;
import smtp.message.client.Subject;

import static smtp.Smtp.Smtp.Smtp.*;

public class SmtpC
{
	private static final String HOST = "smtp.cc.ic.ac.uk";
	private static final int PORT = 25;

	private static final String MAIL_TO = "rhu@doc.ic.ac.uk";
	private static final String RCPT_FROM = "rhu@doc.ic.ac.uk";
	private static final String SUBJECT = "subject";
	private static final String BODY = "body";
	
	public SmtpC() throws Exception
	{
		run();
	}

	public static void main(String[] args) throws Exception
	{
		new SmtpC();
	}

	public void run() throws Exception
	{
		Smtp smtp = new Smtp();
		try (MPSTEndpoint<Smtp, C> se =
				new MPSTEndpoint<>(smtp, C, new SmtpMessageFormatter()))
		{
			se.connect(S, SocketChannelEndpoint::new, HOST, PORT);

			Smtp_C_1 s1 = new Smtp_C_1(se);
			Smtp_C_2 s2 = s1.receive(S, _220, new Buf<>());

			Smtp_C_10 s10 =
					doAuth(
						doSecureEhlo(
								doStartTls(
										doEhlo(s2)
					)));

			Smtp_C_11_Cases s11cases =
					s10.send(S, new Mail(MAIL_TO))
					   .branch(S);
			switch (s11cases.op)
			{
				case _250:
				{
					sendMail(s11cases.receive(_250));
					break;
				}
				case _501:
				{
					s11cases.receive(_501).send(S, new Quit());
					break;
				}
			}
		}
	}

	private Smtp_C_4 doEhlo(Smtp_C_2 s2) throws Exception
	{
		Smtp_C_3 s3 = s2.send(S, new Ehlo("testing1"));
		Buf<Object> b = new Buf<>();
		while (true)
		{	
			Smtp_C_3_Cases s3cases = s3.branch(S);
			switch (s3cases.op)
			{
				case _250:
				{
					Smtp_C_4 s4 = s3cases.receive(_250, b);
					System.out.print("Ehlo: " + b.val);
					return s4;
				}
				case _250d:
				{
					s3 = s3cases.receive(_250d, b);
					System.out.print("Ehlo: " + b.val);
					break;
				}
			}
		}
	}

	private Smtp_C_6 doStartTls(Smtp_C_4 s4) throws Exception
	{
		Buf<Object> b = new Buf<>();
		Smtp_C_6 s6 = s4.send(S, new StartTls()).receive(S, _220, b);
		System.out.print("StartTLS: " + b.val);
		s6.wrapClient(S, SSLSocketChannelWrapper::new);
		return s6;
	}

	private Smtp_C_8 doSecureEhlo(Smtp_C_6 s6) throws Exception
	{
		Smtp_C_7 s7 = s6.send(S, new Ehlo("testing2"));
		Buf<Object> b = new Buf<>();
		while (true)
		{	
			Smtp_C_7_Cases s7cases = s7.branch(S);
			switch(s7cases.op)
			{
				case _250:
				{
					Smtp_C_8 s8 = s7cases.receive(_250, b);
					System.out.print("Ehlo: " + b.val);
					return s8;
				}
				case _250d:
				{
					s7 = s7cases.receive(_250d, b);
					System.out.print("Ehlo: " + b.val);
					break;
				}
			}
		}
	}

	private Smtp_C_10 doAuth(Smtp_C_8 s8) throws Exception
	{
		Smtp_C_9_Cases s9cases = s8.send(S, new Auth(getAuthPlain())).branch(S);
		Buf<Object> b = new Buf<>();
		switch (s9cases.op)
		{
			case _235:
			{
				Smtp_C_10 s10 = s9cases.receive(_235, b);
				System.out.print("Auth: " + b.val);
				return s10;
			}
			case _535:
			{
				s9cases.receive(_535, b).send(S, new Quit());
				System.out.print("Auth: " + b.val);
				System.exit(0);
			}
			default:
			{
				throw new RuntimeException("Shouldn't get in here: " + s9cases.op);
			}
		}
	}

	private void sendMail(Smtp_C_12 s12) throws Exception
	{
		s12.send(S, new Rcpt(RCPT_FROM))
			 .async(S, _250)
			 .send(S, new Data()) 
			 .async(S, _354)
			 .send(S, new Subject(SUBJECT))
			 .send(S, new DataLine(BODY))
			 .send(S, new EndOfData())
			 .receive(S, _250, new Buf<>()) 
			 .send(S, new Quit())
			 .receive(S, _221, new Buf<>());
	}
	

	/*public void run() throws ScribbleRuntimeException, IOException
	{
		String host = "smtp.cc.ic.ac.uk";
		int port = 25;

		Smtp smtp = new Smtp();
		try (SessionEndpoint<Smtp, C> se = new SessionEndpoint<>(smtp, Smtp.C, new SmtpMessageFormatter()))
		{
			se.connect(Smtp.S, SocketChannelEndpoint::new, host, port);

			Smtp_C_1 s1 = new Smtp_C_1(se);
			
			Buf<Smtp_C_1_Future> f220 = new Buf<>();
			Smtp_C_2 s2 = s1.async(Smtp.S, Smtp._220, f220);
			System.out.print("Greeting: " + f220.val.sync().msg);

			Smtp_C_4 s4 = doEhlo(s2);
			Smtp_C_6 s6 = doStartTls(s4);
			Smtp_C_8 s8 = doEhlo(s6);
			Smtp_C_10 s10 = doAuth(s8);

			Smtp_C_11_Cases s11cases = s10.send(Smtp.S, new Mail("rhu@doc.ic.ac.uk")).branch(Smtp.S);
			Smtp_C_12 s12 = null;
			switch (s11cases.op)
			{
				case _250:
				{
					s12 = s11cases.receive(Smtp._250);
					break;
				}
				case _501:  // FIXME: "functional interface" for quit states
				{
					s11cases.receive(Smtp._501).send(Smtp.S, new Quit());
					System.exit(0);
				}
			}
			s12.send(Smtp.S, new Rcpt("rhu@doc.ic.ac.uk"))
			   .async(Smtp.S, Smtp._250)
			   .send(Smtp.S, new Data()) 
			   .async(Smtp.S, Smtp._354)
			   .send(Smtp.S, new Subject("hello ARVI"))
			   .send(Smtp.S, new DataLine("body"))
			   .send(Smtp.S, new EndOfData())
			   .receive(Smtp.S, Smtp._250, new Buf<>())  // Final sync needed for session to be successful?
			   .send(Smtp.S, new Quit());

			/*Case_C_S_501__S_250<?, ?> mailResponse =
					doAuth(
							doEhlo(
									doStartTls(
											doEhlo(new Smtp_C_1(se).async(Smtp.S, Smtp._220), ehlo))
							, ehlo))
					.send(Smtp.S, new Mail(mail))
					.branch(Smtp.S);
			switch (mailResponse.getOp())
			{
				case _250:
				{
					mailResponse.receive(Smtp._250)
						.to(Select_C_S_Rcpt__S_Data.cast).send(Smtp.S, new Rcpt(rcpt))
						.to(Receive_C_S_250.cast).async(Smtp.S, Smtp._250)
						.to(Select_C_S_Rcpt__S_Data.cast).send(Smtp.S, new Data())
						.to(Receive_C_S_354.cast).async(Smtp.S, Smtp._354)
						.to(Select_C_S_DataLine__S_Subject__S_EndOfDate.cast).send(Smtp.S, new Subject(subj))
						.to(Select_C_S_DataLine__S_Subject__S_EndOfDate.cast).send(Smtp.S, new DataLine(body))
						.to(Select_C_S_DataLine__S_Subject__S_EndOfDate.cast).send(Smtp.S, new EndOfData())
						.to(Receive_C_S_250.cast)
							//.async(Smtp.S, Smtp._250)
							.receive(Smtp.S, Smtp._250, new Buf<>())  // Final sync needed for session to be successful?
						.to(Select_C_S_Mail__S_Quit.cast).send(Smtp.S, new Quit());
					break;
				}
				case _501:
				{
					mailResponse.receive(Smtp._501).to(Select_C_S_Mail__S_Quit.cast).send(Smtp.S, new Quit());
				}
			}* /
		}
		catch (Exception e)
		{
			if (e instanceof ScribbleRuntimeException)
			{
				throw (ScribbleRuntimeException) e;
			}
			throw new ScribbleRuntimeException(e);
		}
	}*/

	protected static String getAuthPlain() throws IOException
	{
		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

		String user;
		String pw;

		System.out.println("User: ");
		user = br.readLine();

		System.out.println("Password: ");
		EraserThread et = new EraserThread();
		et.start();
		pw = br.readLine();
		et.stopMasking();

		byte[] u = user.getBytes("utf-8");
		byte[] p = pw.getBytes("utf-8");
		byte[] bs = new byte[u.length + p.length + 2];
		System.arraycopy(u, 0, bs, 1, u.length);
		System.arraycopy(p, 0, bs, u.length + 2, p.length);

		return Base64.getEncoder().encodeToString(bs);
	}
}
