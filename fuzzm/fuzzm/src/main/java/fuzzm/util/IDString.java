/* 
 * Copyright (C) 2018, Rockwell Collins
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the 3-clause BSD license.  See the LICENSE file for details.
 * 
 */
package fuzzm.util;

public class IDString {
    private final String prefix;
    private final String base;
    private IDString(String prefix, String base) {
        this.prefix = prefix;
        this.base   = ID.cleanString(base);
    }
    public static IDString newID(String base) {
        return new IDString("",base);
    }
    public static IDString newID(String prefix, String base, long index) {
        return new IDString(prefix + "_" + index,base);
    }
    public IDString index(long index) {
        return newID(prefix,base,index);
    }
    public IDString prefix(String prefix) {
        return new IDString(prefix,base);
    }
    public String name() {
        return "__" + prefix + "_" + base;
    }
    @Override
    public String toString() {
        throw new IllegalArgumentException();
    }
}
