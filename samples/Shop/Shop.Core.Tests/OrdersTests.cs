using CsVerify;
using Shop.Core;
using Xunit;

public class OrdersTests
{
    [Fact]
    public void FirstOver_FindsTheFirst() => Assert.Equal(1, Orders.FirstOver(new[] { 5, 50, 70 }, 10));

    [Fact]
    public void FirstOver_None() => Assert.Equal(-1, Orders.FirstOver(new[] { 5, 7 }, 10));

    [Fact]
    public void Total_Sums() => Assert.Equal(12L, Orders.Total(new[] { 5, 7 }));

    [Fact]
    public void Discount_ForMembersOver100() => Assert.Equal(15, Orders.Discount(150, true));

    [Fact]
    public void Discount_NotForOthers() => Assert.Equal(0, Orders.Discount(150, false));

    [Fact]
    public void Last_IsTheLast() => Assert.Equal(7, Orders.Last(new[] { 5, 7 }, Ghost.Of(2)));

    [Fact]
    public void CanShip_WhenPaidAndInStock() => Assert.True(Orders.CanShip(true, true, false));
}
