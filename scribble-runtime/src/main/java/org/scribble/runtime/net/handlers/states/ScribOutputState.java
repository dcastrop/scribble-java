package org.scribble.runtime.net.handlers.states;

abstract public class ScribOutputState extends ScribState
{
	public ScribOutputState(String name)
	{
		super(name);
	}

	@Override
	protected boolean canEqual(Object o)
	{
		return o instanceof ScribOutputState;
	}
}