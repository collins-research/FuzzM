package jfuzz.util;

/**
 * An interface that describes how to 
 * 1) update the internal representation of some visual object,
 * 2) write it to some external representation(i.e. an image), and 
 * 3) reset the internal representation to a blank state.
 *
 */

//TODO: delete this interface
public interface DisplayObject {

	public void update(RatSignal rs);
	public void write();
	public void reset();
}
