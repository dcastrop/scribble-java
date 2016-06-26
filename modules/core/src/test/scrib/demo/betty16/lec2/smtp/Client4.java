package demo.betty16.lec2.smtp;

import static demo.betty16.lec2.smtp.Smtp.Smtp.Smtp.S;
import static demo.betty16.lec2.smtp.Smtp.Smtp.Smtp._220;

import java.io.IOException;

import org.scribble.main.ScribbleRuntimeException;
import org.scribble.net.Buf;
import org.scribble.net.session.SessionEndpoint;
import org.scribble.net.session.SocketChannelEndpoint;

import demo.betty16.lec2.smtp.Smtp.Smtp.Smtp;
import demo.betty16.lec2.smtp.Smtp.Smtp.channels.C.Smtp_C_1;
import demo.betty16.lec2.smtp.Smtp.Smtp.channels.C.Smtp_C_3;
import demo.betty16.lec2.smtp.Smtp.Smtp.channels.C.Smtp_C_3_Handler;
import demo.betty16.lec2.smtp.Smtp.Smtp.channels.C.Smtp_C_4;
import demo.betty16.lec2.smtp.Smtp.Smtp.channels.C.Smtp_C_7;
import demo.betty16.lec2.smtp.Smtp.Smtp.channels.C.Smtp_C_7_Handler;
import demo.betty16.lec2.smtp.Smtp.Smtp.channels.C.Smtp_C_8;
import demo.betty16.lec2.smtp.Smtp.Smtp.roles.C;
import demo.betty16.lec2.smtp.message.SmtpMessageFormatter;
import demo.betty16.lec2.smtp.message.client.Ehlo;
import demo.betty16.lec2.smtp.message.client.Quit;
import demo.betty16.lec2.smtp.message.client.StartTls;
import demo.betty16.lec2.smtp.message.server._250;
import demo.betty16.lec2.smtp.message.server._250d;

public class Client4 {

	public static void main(String[] args) throws Exception
	{
		String host = "smtp.cc.ic.ac.uk";
		int port = 25;

		Smtp smtp = new Smtp();
		try (SessionEndpoint<Smtp, C> se = new SessionEndpoint<>(smtp, Smtp.C, new SmtpMessageFormatter()))
		{
			se.connect(Smtp.S, SocketChannelEndpoint::new, host, port);
			new Client4().run(new Smtp_C_1(se));
		}
	}

	private void run(Smtp_C_1 c1) throws Exception {
		c1.async(S, _220).send(S, new Ehlo("test")).branch(S, new MySmtp_C_3Handler());
	}
}
	
class MySmtp_C_3Handler implements Smtp_C_3_Handler {

	@Override
	public void receive(Smtp_C_3 s3, demo.betty16.lec2.smtp.Smtp.Smtp.ops._250d op, Buf<_250d> arg) throws ScribbleRuntimeException, IOException, ClassNotFoundException
	{
		s3.branch(S, this);
	}

	@Override
	public void receive(Smtp_C_4 s4, demo.betty16.lec2.smtp.Smtp.Smtp.ops._250 op, Buf<_250> arg) throws ScribbleRuntimeException, IOException, ClassNotFoundException
	{
		s4.send(S, new StartTls()).async(S, _220).send(S, new Ehlo("test")).branch(S, new MySmtp_C_8Handler());
	}
}

class MySmtp_C_8Handler implements Smtp_C_7_Handler {

	@Override
	public void receive(Smtp_C_7 s7, demo.betty16.lec2.smtp.Smtp.Smtp.ops._250d op, Buf<_250d> arg) throws ScribbleRuntimeException, IOException, ClassNotFoundException
	{
		s7.branch(S, this);
	}

	@Override
	public void receive(Smtp_C_8 s8, demo.betty16.lec2.smtp.Smtp.Smtp.ops._250 op, Buf<_250> arg) throws ScribbleRuntimeException, IOException, ClassNotFoundException
	{
		s8.send(S, new Quit());
	}
}