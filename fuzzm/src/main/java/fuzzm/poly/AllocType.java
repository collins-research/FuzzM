package jfuzz.poly;

public enum AllocType {
	
	  EQ(0x8FFFFFFF,0x00000000),
	  IN(0x8FFFFFFF,0x00000000),
	  UF(0x9FFFFFFF,0x00000000),
	   K(0xAFFFFFFF,0x00000000),
	   M(0xBFFFFFFF,0x00000000);

	public final int andmask;
	public final int ormask;
	
	private AllocType(int andmask, int ormask) {
		this.andmask = andmask;
		this.ormask  = ormask;
	}
	
}
