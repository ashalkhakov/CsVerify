namespace Layered.Model;

// a member internal to the projects the project file's InternalsVisibleTo grants (#116)
public sealed class Account
{
    internal long RowId { get; set; }
}
