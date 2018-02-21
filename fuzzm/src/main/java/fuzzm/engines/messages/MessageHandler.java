package jfuzz.engines.messages;

public abstract class MessageHandler {
	
	public void handleMessage(Message message) {
		message.handleAccept(this);
	}

	protected void handleMessage(CounterExampleMessage m) {
	}
	
	protected void handleMessage(GeneralizedMessage m) {
	}

	protected void handleMessage(TestVectorMessage m) {
	}

	protected void handleMessage(ConstraintMessage m) {
	}
	
	protected void handleMessage(UnsatMessage m) {
	}
	
	protected void handleMessage(IntervalVectorMessage m) {
	}
	
	protected void handleMessage(PauseMessage m) {
	}
	
	protected void handleMessage(ResumeMessage m) {
	}
	
	abstract protected void handleMessage(ExitMessage m);
	
}
