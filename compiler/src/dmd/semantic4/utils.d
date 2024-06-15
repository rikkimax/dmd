module dmd.semantic4.utils;
import dmd.tokens;
import dmd.astenums;
import dmd.mtype;

bool isTypePointer(Type type)
{
    if (type is null)
        return false;

    switch (type.ty)
    {
    case TY.Tarray, TY.Taarray, TY.Tpointer, TY.Treference, TY.Tfunction,
            TY.Tclass, TY.Tdelegate:
            return true;

    case TY.Tstruct:
        TypeStruct type2 = type.isTypeStruct();
        return type2 !is null ? type2.sym.hasPointerField : false;

    default:
        return false;
    }
}

bool isTyWithoutValue(TY ty)
{
    switch (ty)
    {
    case TY.Tnone, TY.Tvoid, TY.Tnoreturn:
        return true;

    default:
        return false;
    }
}

bool isEXPLiteral(EXP exp)
{
    switch (exp)
    {
    case EXP.null_, EXP.arrayLiteral, EXP.assocArrayLiteral, EXP.structLiteral,
            EXP.string_, EXP.this_, EXP.int64, EXP.float64, EXP.complex80,
            EXP.compoundLiteral, EXP.blit:
            return true;

    default:
        return false;
    }
}

bool isPointerMutable(StorageClass storedIn, Type from, Type viaType)
{
    if (!from.isTypePointer || isTyWithoutValue(from.ty))
        return false;
    else if ((storedIn & (STC.const_ | STC.immutable_)) != 0)
        return false;
    else if (!viaType.isMutable())
        return false;

    if (auto da = viaType.isTypeDArray)
    {
        if ((da.next.mod & (MODFlags.const_ | MODFlags.immutable_)) != 0)
            return false;
    }

    return true;
}
