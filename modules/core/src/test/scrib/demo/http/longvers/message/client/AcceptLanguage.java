package demo.http.longvers.message.client;

import demo.http.longvers.HttpLong.Http.Http;
import demo.http.longvers.message.HeaderField;

public class AcceptLanguage extends HeaderField
{
	private static final long serialVersionUID = 1L;

	public AcceptLanguage(String text)
	{
		super(Http.ACCEPTL, text);
	}
}