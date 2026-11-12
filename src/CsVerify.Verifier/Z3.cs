using System;
using System.IO;
using System.Linq;

namespace CsVerify.Verifier
{
    /// <summary>Where Z3, the solver Boogie runs, is: given, CSVERIFY_Z3, or on the PATH.</summary>
    public static class Z3
    {
        public static string Find(string explicitPath)
        {
            if (!string.IsNullOrEmpty(explicitPath)) return explicitPath;
            var env = Environment.GetEnvironmentVariable("CSVERIFY_Z3");
            if (!string.IsNullOrEmpty(env)) return env;
            var exe = OperatingSystem.IsWindows() ? "z3.exe" : "z3";
            var dirs = (Environment.GetEnvironmentVariable("PATH") ?? "").Split(Path.PathSeparator)
                .Concat(new[] { "/opt/homebrew/bin", "/usr/local/bin", "/usr/bin" });
            foreach (var d in dirs)
            {
                if (string.IsNullOrEmpty(d)) continue;
                var p = Path.Combine(d, exe);
                if (File.Exists(p)) return p;
            }
            throw new FileNotFoundException("Z3 not found: install it (brew install z3 / apt install z3 / winget install z3) or set CSVERIFY_Z3.");
        }
    }
}
