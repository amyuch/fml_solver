def sv_int_to_python(val_str: str) -> int:
    if not val_str:
        return 0
    val_str = val_str.replace("_", "").lower()
    if val_str.startswith("'h"):
        return int(val_str[2:], 16)
    elif val_str.startswith("'d"):
        return int(val_str[2:], 10)
    elif val_str.startswith("'b"):
        return int(val_str[2:], 2)
    elif val_str.startswith("'o"):
        return int(val_str[2:], 8)
    elif val_str.startswith("0x"):
        return int(val_str, 16)
    elif val_str.startswith("0b"):
        return int(val_str, 2)
    elif val_str.startswith("0") and len(val_str) > 1:
        return int(val_str, 8)
    else:
        return int(val_str, 10)
