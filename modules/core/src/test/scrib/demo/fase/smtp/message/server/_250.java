package demo.fase.smtp.message.server;

import demo.fase.smtp.Smtp.Smtp.Smtp;
import demo.fase.smtp.message.SmtpMessage;

public class _250 extends SmtpMessage
{
	private static final long serialVersionUID = 1L;

	public _250()
	{
		super(Smtp._250);
	}

	public _250(String body)
	{
		super(Smtp._250, body);
	}
}