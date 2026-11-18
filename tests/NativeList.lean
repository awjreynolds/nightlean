import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium

noctium_circuit memoInput where
  private owner : Bytes32
  private spender : Bytes32
  private x : Native
  private y : Native
  public enabled : Bool
end

noctium_contract NativeList where
  list inbox : struct Memo {
    x : Native
    y : Native
  }
  tree memos : Bytes32 => Bytes32 => List struct Memo {
    x : Native
    y : Native
  }
  entry append uses memoInput where
    member memos[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert memos[disclose(owner)] := emptyMap
    } else {
    }
    member memos[disclose(owner)][disclose(spender)] as memoPresent
    if eq(memoPresent, false) then {
      reset memos[disclose(owner)][disclose(spender)]
    } else {
    }
    pushFront inbox := fields(disclose(x), disclose(y))
    pushFront memos[disclose(owner)][disclose(spender)] := fields(disclose(x), disclose(y))
    length inbox as inboxLength
    head inbox as inboxHead
    length memos[disclose(owner)][disclose(spender)] as memoLength
    head memos[disclose(owner)][disclose(spender)] as memoHead
    require eq(inboxHead_x, x)
    require eq(inboxHead_y, y)
    require eq(memoHead_x, x)
    require eq(memoHead_y, y)
  end
  entry pop uses memoInput where
    popFront inbox
    popFront memos[disclose(owner)][disclose(spender)]
  end
  entry clear uses memoInput where
    reset inbox
    reset memos[disclose(owner)][disclose(spender)]
    length inbox as inboxLengthAfterClear
    length memos[disclose(owner)][disclose(spender)] as memoLengthAfterClear
    require eq(inboxLengthAfterClear, uint(0))
    require eq(memoLengthAfterClear, uint(0))
  end
  entry guarded uses memoInput where
    when enabled pushFront inbox := fields(disclose(x), disclose(y))
    when enabled pushFront memos[disclose(owner)][disclose(spender)] := fields(disclose(x), disclose(y))
    when enabled length memos[disclose(owner)][disclose(spender)] as guardedLength
    when enabled head memos[disclose(owner)][disclose(spender)] as guardedHead
  end
  entry inspect uses memoInput where
    length inbox as inboxLength
    head inbox as inboxHead
    length memos[disclose(owner)][disclose(spender)] as memoLength
    head memos[disclose(owner)][disclose(spender)] as memoHead
  end
end
