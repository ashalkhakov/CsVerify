#nullable enable
namespace CsVerify.Bcl
{
    using System.IO;
    using System.IO.Compression;
    using System.Threading;

    // The library types whose objects must be disposed (DisposalAnalyzer): they hold a file, a socket, a timer, a
    // handle. Each stub class marks its type [MustDispose]; a constructor that takes the stream it wraps says so with
    // [TakesOwnership]. (MemoryStream, StringReader, Task and HttpClient, meant to be shared, are left out: disposing
    // them is harmless or wrong, not required.)

    [ContractsFor(typeof(FileStream)), MustDispose] public static class FileStreamDisposal { }
    [ContractsFor(typeof(FileSystemWatcher)), MustDispose] public static class FileSystemWatcherDisposal { }
    [ContractsFor(typeof(Timer)), MustDispose] public static class TimerDisposal { }
    [ContractsFor(typeof(System.Timers.Timer)), MustDispose] public static class TimersTimerDisposal { }
    [ContractsFor(typeof(CancellationTokenSource)), MustDispose] public static class CancellationTokenSourceDisposal { }
    [ContractsFor(typeof(Mutex)), MustDispose] public static class MutexDisposal { }
    [ContractsFor(typeof(System.Diagnostics.Process)), MustDispose] public static class ProcessDisposal { }
    [ContractsFor(typeof(System.Net.Sockets.Socket)), MustDispose] public static class SocketDisposal { }
    [ContractsFor(typeof(System.Net.Sockets.TcpClient)), MustDispose] public static class TcpClientDisposal { }
    [ContractsFor(typeof(System.Net.Http.HttpResponseMessage)), MustDispose] public static class HttpResponseMessageDisposal { }
    [ContractsFor(typeof(System.Data.Common.DbConnection)), MustDispose] public static class DbConnectionDisposal { }
    [ContractsFor(typeof(System.Data.Common.DbCommand)), MustDispose] public static class DbCommandDisposal { }
    [ContractsFor(typeof(System.Data.Common.DbDataReader)), MustDispose] public static class DbDataReaderDisposal { }

    [ContractsFor(typeof(StreamReader)), MustDispose]
    public static class StreamReaderDisposal
    {
        public static StreamReader @new([TakesOwnership] Stream stream) => throw null!;
        public static StreamReader @new([TakesOwnership] Stream stream, System.Text.Encoding encoding) => throw null!;
    }

    [ContractsFor(typeof(StreamWriter)), MustDispose]
    public static class StreamWriterDisposal
    {
        public static StreamWriter @new([TakesOwnership] Stream stream) => throw null!;
        public static StreamWriter @new([TakesOwnership] Stream stream, System.Text.Encoding encoding) => throw null!;
    }

    [ContractsFor(typeof(BinaryReader)), MustDispose]
    public static class BinaryReaderDisposal
    {
        public static BinaryReader @new([TakesOwnership] Stream input) => throw null!;
    }

    [ContractsFor(typeof(BinaryWriter)), MustDispose]
    public static class BinaryWriterDisposal
    {
        public static BinaryWriter @new([TakesOwnership] Stream output) => throw null!;
    }

    [ContractsFor(typeof(GZipStream)), MustDispose]
    public static class GZipStreamDisposal
    {
        public static GZipStream @new([TakesOwnership] Stream stream, CompressionMode mode) => throw null!;
    }
}
