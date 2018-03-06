/*
 * Derived From: SciJava Common shared library for SciJava software.
 *
 * Copyright (C) 2009 - 2017 Board of Regents of the University of
 * Wisconsin-Madison, Broad Institute of MIT and Harvard, and Max Planck
 * Institute of Molecular Cell Biology and Genetics.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 * #L%
 */
package fuzzm.solver;

import java.io.File;
import java.io.FileInputStream;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;

public class PathUtils {
    /** Gets the name of the operating system. */
    public static String osName() {
        final String osName = System.getProperty("os.name");
        return osName == null ? "Unknown" : osName;
    }
    public static boolean isWindows() {
        return osName().startsWith("Win");
    }   
    /**
     * Gets the base location of the given class.
     * <p>
     * If the class is directly on the file system (e.g.,
     * "/path/to/my/package/MyClass.class") then it will return the base directory
     * (e.g., "file:/path/to").
     * </p>
     * <p>
     * If the class is within a JAR file (e.g.,
     * "/path/to/my-jar.jar!/my/package/MyClass.class") then it will return the
     * path to the JAR (e.g., "file:/path/to/my-jar.jar").
     * </p>
     *
     * @param c The class whose location is desired.
     * @see FileUtils#urlToFile(URL) to convert the result to a {@link File}.
     */
    public static URL getLocation(final Class<?> c) throws MalformedURLException {
        URL url = ClassLoader.getSystemClassLoader().getResource(".");

        if (url != null) return url;
        
        if (c == null) return null; // could not load the class

        // try the easy way first
        try {
            final URL codeSourceLocation =
                c.getProtectionDomain().getCodeSource().getLocation();
            if (codeSourceLocation != null) return codeSourceLocation;
        }
        catch (final SecurityException e) {
            // NB: Cannot access protection domain.
        }
        catch (final NullPointerException e) {
            // NB: Protection domain or code source is null.
        }

        // NB: The easy way failed, so we try the hard way. We ask for the class
        // itself as a resource, then strip the class's path from the URL string,
        // leaving the base path.

        // get the class's raw resource path
        final URL classResource = c.getResource(c.getSimpleName() + ".class");
        if (classResource == null) return null; // cannot find class resource

        final String urlString = classResource.toString();
        final String suffix = c.getCanonicalName().replace('.', '/') + ".class";
        if (!urlString.endsWith(suffix)) return null; // weird URL

        // strip the class's path from the URL string
        final String base = urlString.substring(0, urlString.length() - suffix.length());

        String path = base;

        // remove the "jar:" prefix and "!/" suffix, if present
        if (path.startsWith("jar:")) path = path.substring(4, path.length() - 2);
        
        return new URL(path);
    } 
    /**
     * Converts the given URL string to its corresponding {@link File}.
     * 
     * @param url The URL to convert.
     * @return A file path suitable for use with e.g. {@link FileInputStream}
     * @throws IllegalArgumentException if the URL does not correspond to a file.
     */
    public static File urlToFile(final String url) {
        String path = url;
        if (path.startsWith("jar:")) {
            // remove "jar:" prefix and "!/" suffix
            final int index = path.indexOf("!/");
            path = path.substring(4, index);
        }
        try {
            if (isWindows() && path.matches("file:[A-Za-z]:.*")) {
                path = "file:/" + path.substring(5);
            }
            return new File(new URL(path).toURI());
        }
        catch (final MalformedURLException e) {
            // NB: URL is not completely well-formed.
        }
        catch (final URISyntaxException e) {
            // NB: URL is not completely well-formed.
        }
        if (path.startsWith("file:")) {
            // pass through the URL as-is, minus "file:" prefix
            path = path.substring(5);
            return new File(path);
        }
        throw new IllegalArgumentException("Invalid URL: " + url);
    }
    /**
     * Computes the Absolute Path to either the running Jar file. 
     * 
     * @return An Absolute File Path String.
     */
    public static String pathToRunningJar() {
        try {
            URL url = getLocation(PathUtils.class);
            if (url == null) return ".";            
            return urlToFile(url.toString()).getAbsolutePath();
        } catch (MalformedURLException e) {
           return ".";
        }
    }


}
