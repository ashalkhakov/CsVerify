#nullable enable
namespace CsVerify.Bcl
{
    using System.Threading;
    using System.Threading.Channels;

    // What stays the same about these, for all that goes on behind them: a channel has one reader and one writer, and a
    // source one token. What they hold, or whether it has been cancelled, can change at any moment, so it isn't said.

    [ContractsFor(typeof(Channel<,>))]
    public static class ChannelContracts<TWrite, TRead>
    {
        [Pure] public static ChannelReader<TRead> get_Reader(Channel<TWrite, TRead> @this) => throw null!;
        [Pure] public static ChannelWriter<TWrite> get_Writer(Channel<TWrite, TRead> @this) => throw null!;
    }

    [ContractsFor(typeof(CancellationTokenSource))]
    public static class CancellationTokenSourceContracts
    {
        [Pure] public static CancellationToken get_Token(CancellationTokenSource @this) => throw null!;
    }
}
