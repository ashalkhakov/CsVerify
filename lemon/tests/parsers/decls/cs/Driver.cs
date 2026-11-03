// Feeds the parser the tokens of a file: one per line, its code and its value.
using System.Collections.Generic;
using System.IO;

public static class Driver
{
    public static void Main(string[] args)
    {
        var codes = new List<int>();
        var values = new List<object?>();
        foreach (string line in File.ReadAllLines(args[0]))
        {
            string[] parts = line.Split(' ', System.StringSplitOptions.RemoveEmptyEntries);
            if (parts.Length < 2) continue;
            codes.Add(int.Parse(parts[0]));
            values.Add(int.Parse(parts[1]));
        }
        ParseParser.Parse(codes.ToArray(), values.ToArray(), new ParseParser.Totals());
    }
}
