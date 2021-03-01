const

  NODE_NUM : 2;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);
  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
    CacheData : DATA;
  end;
  new_type_0 : array [ NODE ] of boolean;
  new_type_1 : array [ NODE ] of boolean;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : ABS_NODE;
    ShrVld : boolean;
    InvSet : new_type_0;
    ShrSet : new_type_1;
    HomeHeadPtr : boolean;
    HomeShrSet : boolean;
    HomeInvSet : boolean;
    HomeUniMsg : boolean;
  end;

  UNI_CMD : enum {UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : ABS_NODE;
    HomeProc : boolean;
    Data : DATA;
  end;

  INV_CMD : enum {INV_None, INV_Inv, INV_InvAck};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {RP_None, RP_Replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {WB_None, WB_Wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : ABS_NODE;
    HomeProc : boolean;
    Data : DATA;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : ABS_NODE;
    HomeProc : boolean;
    Data : DATA;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;
  new_type_2 : array [ NODE ] of NODE_STATE;
  new_type_3 : array [ NODE ] of UNI_MSG;
  new_type_4 : array [ NODE ] of INV_MSG;
  new_type_5 : array [ NODE ] of RP_MSG;

  STATE : record
  -- Program variables:
    Proc : new_type_2;
    Dir : DIR_STATE;
    MemData : DATA;
    UniMsg : new_type_3;
    InvMsg : new_type_4;
    RpMsg : new_type_5;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
    HomeProc : NODE_STATE;
    HomeUniMsg : UNI_MSG;
    HomeInvMsg : INV_MSG;
    HomeRpMsg : RP_MSG;
  -- Auxiliary variables:
    CurrData : DATA;
    PrevData : DATA;
    LastWrVld : boolean;
    LastWrPtr : ABS_NODE;
    PendReqSrc : ABS_NODE;
    PendReqCmd : UNI_CMD;
    Collecting : boolean;
    FwdCmd : UNI_CMD;
    FwdSrc : ABS_NODE;
    LastInvAck : ABS_NODE;
    LastOtherInvAck : ABS_NODE;
  end;

var

  Sta : STATE;

--------------------------------------------------------

ruleset h : NODE; d : DATA do
startstate "Init"
  undefine Sta;
  Sta.MemData := d;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.NakcMsg.Cmd := NAKC_None;
  for p : NODE do
    Sta.Proc[p].ProcCmd := NODE_None;
    Sta.Proc[p].InvMarked := false;
    Sta.Proc[p].CacheState := CACHE_I;
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
    Sta.UniMsg[p].Cmd := UNI_None;
    Sta.InvMsg[p].Cmd := INV_None;
    Sta.RpMsg[p].Cmd := RP_None;
    Sta.UniMsg[p].HomeProc := false;
  end;
  Sta.HomeUniMsg.HomeProc := false;
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeRpMsg.Cmd := RP_None;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.CurrData := d;
  Sta.PrevData := d;
  Sta.LastWrVld := false;
  Sta.Collecting := false;
  Sta.FwdCmd := UNI_None;
endstartstate;
endruleset;

ruleset src : NODE; data : DATA do
rule "Store"
  Sta.Proc[src].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[src].CacheData := data;
  NxtSta.CurrData := data;
  NxtSta.LastWrVld := true;
  NxtSta.LastWrPtr := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; data : DATA do
rule "Store_Home"
  Sta.HomeProc.CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeProc.CacheData := data;
  NxtSta.CurrData := data;
  NxtSta.LastWrVld := true;
  NxtSta.LastWrPtr := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "PI_Remote_Get"
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[src].ProcCmd := NODE_Get;
  NxtSta.UniMsg[src].Cmd := UNI_Get;
  NxtSta.HomeUniMsg.HomeProc := true;
  undefine NxtSta.UniMsg[src].Data;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "PI_Remote_Get_Home"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_I
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeProc.ProcCmd := NODE_Get;
  NxtSta.HomeUniMsg.Cmd := UNI_Get;
  NxtSta.HomeUniMsg.HomeProc := true;
  undefine NxtSta.HomeUniMsg.Data;
  Sta := NxtSta;
endrule;
endruleset;

rule "PI_Local_Get_Get"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_I &
  !Sta.Dir.Pending & Sta.Dir.Dirty
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeProc.ProcCmd := NODE_Get;
  NxtSta.Dir.Pending := true;
  NxtSta.HomeUniMsg.Cmd := UNI_Get;
  NxtSta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  undefine NxtSta.HomeUniMsg.Data;
  NxtSta.PendReqCmd := UNI_Get;
  NxtSta.Collecting := false;
  Sta := NxtSta;
endrule;

rule "PI_Local_Get_Put"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_I &
  !Sta.Dir.Pending & !Sta.Dir.Dirty
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Dir.Local := true;
  NxtSta.HomeProc.ProcCmd := NODE_None;
  if (Sta.HomeProc.InvMarked) then
    NxtSta.HomeProc.InvMarked := false;
    NxtSta.HomeProc.CacheState := CACHE_I;
    undefine NxtSta.HomeProc.CacheData;
  else
    NxtSta.HomeProc.CacheState := CACHE_S;
    NxtSta.HomeProc.CacheData := Sta.MemData;
  end;
  Sta := NxtSta;
endrule;

ruleset src : NODE do
rule "PI_Remote_GetX"
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[src].ProcCmd := NODE_GetX;
  NxtSta.UniMsg[src].Cmd := UNI_GetX;
  NxtSta.UniMsg[src].HomeProc := true;
  undefine NxtSta.UniMsg[src].Data;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "PI_Remote_GetX_Home"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_I
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeProc.ProcCmd := NODE_GetX;
  NxtSta.HomeUniMsg.Cmd := UNI_GetX;
  NxtSta.HomeUniMsg.HomeProc := true;
  undefine NxtSta.HomeUniMsg.Data;
  Sta := NxtSta;
endrule;
endruleset;

rule "PI_Local_GetX_GetX"
  Sta.HomeProc.ProcCmd = NODE_None &
  ( Sta.HomeProc.CacheState = CACHE_I |
    Sta.HomeProc.CacheState = CACHE_S ) &
  !Sta.Dir.Pending & Sta.Dir.Dirty
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeProc.ProcCmd := NODE_GetX;
  NxtSta.Dir.Pending := true;
  NxtSta.HomeUniMsg.Cmd := UNI_GetX;
  NxtSta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  undefine NxtSta.HomeUniMsg.Data;
  NxtSta.PendReqCmd := UNI_GetX;
  NxtSta.Collecting := false;
  Sta := NxtSta;
endrule;

rule "PI_Local_GetX_PutX"
  Sta.HomeProc.ProcCmd = NODE_None &
  ( Sta.HomeProc.CacheState = CACHE_I |
    Sta.HomeProc.CacheState = CACHE_S ) &
  !Sta.Dir.Pending & !Sta.Dir.Dirty
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Dir.Local := true;
  NxtSta.Dir.Dirty := true;
  if (Sta.Dir.HeadVld) then
    NxtSta.Dir.Pending := true;
    NxtSta.Dir.HeadVld := false;
    undefine NxtSta.Dir.HeadPtr;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      if (( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
             Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p ) ) then
        NxtSta.Dir.InvSet[p] := true;
        NxtSta.InvMsg[p].Cmd := INV_Inv;
      else
        NxtSta.Dir.InvSet[p] := false;
        NxtSta.InvMsg[p].Cmd := INV_None;
      end;
    end;
    NxtSta.Dir.HomeShrSet := false;
    NxtSta.Dir.HomeInvSet := false;
    NxtSta.HomeInvMsg.Cmd := INV_None;
    NxtSta.Collecting := true;
    NxtSta.PrevData := Sta.CurrData;
    NxtSta.LastOtherInvAck := Sta.Dir.HeadPtr;
  end;
  NxtSta.HomeProc.ProcCmd := NODE_None;
  NxtSta.HomeProc.InvMarked := false;
  NxtSta.HomeProc.CacheState := CACHE_E;
  NxtSta.HomeProc.CacheData := Sta.MemData;
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "PI_Remote_PutX"
  Sta.Proc[dst].ProcCmd = NODE_None &
  Sta.Proc[dst].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[dst].CacheState := CACHE_I;
  undefine NxtSta.Proc[dst].CacheData;
  NxtSta.WbMsg.Cmd := WB_Wb;
  NxtSta.WbMsg.Proc := dst;
  NxtSta.WbMsg.Data := Sta.Proc[dst].CacheData;
  Sta := NxtSta;
endrule;
endruleset;

rule "PI_Local_PutX"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  if (Sta.Dir.Pending) then
    NxtSta.HomeProc.CacheState := CACHE_I;
    undefine NxtSta.HomeProc.CacheData;
    NxtSta.Dir.Dirty := false;
    NxtSta.MemData := Sta.HomeProc.CacheData;
  else
    NxtSta.HomeProc.CacheState := CACHE_I;
    undefine NxtSta.HomeProc.CacheData;
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := false;
    NxtSta.MemData := Sta.HomeProc.CacheData;
  end;
  Sta := NxtSta;
endrule;

ruleset src : NODE do
rule "PI_Remote_Replace"
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_S
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[src].CacheState := CACHE_I;
  undefine NxtSta.Proc[src].CacheData;
  NxtSta.RpMsg[src].Cmd := RP_Replace;
  Sta := NxtSta;
endrule;
endruleset;

rule "PI_Local_Replace"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_S
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Dir.Local := false;
  NxtSta.HomeProc.CacheState := CACHE_I;
  undefine NxtSta.HomeProc.CacheData;
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "NI_Nak"
  Sta.UniMsg[dst].Cmd = UNI_Nak
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.UniMsg[dst].Cmd := UNI_None;
  undefine NxtSta.UniMsg[dst].Proc;
  undefine NxtSta.UniMsg[dst].Data;
  NxtSta.Proc[dst].ProcCmd := NODE_None;
  NxtSta.Proc[dst].InvMarked := false;
  Sta := NxtSta;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Nak_Home"
  Sta.HomeUniMsg.Cmd = UNI_Nak
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeUniMsg.Cmd := UNI_None;
  undefine NxtSta.HomeUniMsg.Proc;
  undefine NxtSta.HomeUniMsg.Data;
  NxtSta.HomeProc.ProcCmd := NODE_None;
  NxtSta.HomeProc.InvMarked := false;
  Sta := NxtSta;
endrule;
endruleset;

rule "NI_Nak_Clear"
  Sta.NakcMsg.Cmd = NAKC_Nakc
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.NakcMsg.Cmd := NAKC_None;
  NxtSta.Dir.Pending := false;
  Sta := NxtSta;
endrule;

ruleset src : NODE do
rule "NI_Local_Get_Nak"
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].HomeProc = true &
  Sta.RpMsg[src].Cmd != RP_Replace &
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty & Sta.Dir.Local & Sta.HomeProc.CacheState != CACHE_E |
    Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr = src )
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].HomeProc := true;
  undefine NxtSta.UniMsg[src].Data;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Get"
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].HomeProc = true &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr != src
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Dir.Pending := true;
  NxtSta.UniMsg[src].Cmd := UNI_Get;
  NxtSta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  undefine NxtSta.UniMsg[src].Data;
  NxtSta.PendReqSrc := src;
  NxtSta.PendReqCmd := UNI_Get;
  NxtSta.Collecting := false;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Put"
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].HomeProc = true &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending &
  (Sta.Dir.Dirty -> Sta.Dir.Local & Sta.HomeProc.CacheState = CACHE_E)
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  if (Sta.Dir.Dirty) then
    NxtSta.Dir.Dirty := false;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := src;
    NxtSta.MemData := Sta.HomeProc.CacheData;
    NxtSta.HomeProc.CacheState := CACHE_S;
    NxtSta.UniMsg[src].Cmd := UNI_Put;
    NxtSta.UniMsg[src].HomeProc := true;
    NxtSta.UniMsg[src].Data := Sta.HomeProc.CacheData;
  else
    if (Sta.Dir.HeadVld) then
      NxtSta.Dir.ShrVld := true;
      NxtSta.Dir.ShrSet[src] := true;
      for p : NODE do
        NxtSta.Dir.InvSet[p] := (p = src) | Sta.Dir.ShrSet[p];
        NxtSta.Dir.HomeInvSet := (p = src) | Sta.Dir.HomeShrSet;
      end;
    else
      NxtSta.Dir.HeadVld := true;
      NxtSta.Dir.HeadPtr := src;
    end;
    NxtSta.UniMsg[src].Cmd := UNI_Put;
    NxtSta.UniMsg[src].HomeProc := true;
    NxtSta.UniMsg[src].Data := Sta.MemData;
  end;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Nak"
  src != dst &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].Proc := dst;
  undefine NxtSta.UniMsg[src].Data;
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Nak_Home"
  src != dst &
  Sta.HomeUniMsg.Cmd = UNI_Get &
  Sta.HomeUniMsg.Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeUniMsg.Cmd := UNI_Nak;
  NxtSta.HomeUniMsg.Proc := dst;
  undefine NxtSta.HomeUniMsg.Data;
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Put"
  src != dst &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[dst].CacheState := CACHE_S;
  NxtSta.UniMsg[src].Cmd := UNI_Put;
  NxtSta.UniMsg[src].Proc := dst;
  NxtSta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Put_Home"
  src != dst &
  Sta.HomeUniMsg.Cmd = UNI_Get &
  Sta.HomeUniMsg.Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[dst].CacheState := CACHE_S;
  NxtSta.HomeUniMsg.Cmd := UNI_Put;
  NxtSta.HomeUniMsg.Proc := dst;
  NxtSta.HomeUniMsg.Data := Sta.Proc[dst].CacheData;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_Nak"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc = true &
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty & Sta.Dir.Local & Sta.HomeProc.CacheState != CACHE_E |
    Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr = src )
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].HomeProc := true;
  undefine NxtSta.UniMsg[src].Data;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_GetX"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc = true &
  !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr != src
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Dir.Pending := true;
  NxtSta.UniMsg[src].Cmd := UNI_GetX;
  NxtSta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  undefine NxtSta.UniMsg[src].Data;
  NxtSta.PendReqSrc := src;
  NxtSta.PendReqCmd := UNI_GetX;
  NxtSta.Collecting := false;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX"
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].HomeProc = true &
  !Sta.Dir.Pending &
  (Sta.Dir.Dirty -> Sta.Dir.Local & Sta.HomeProc.CacheState = CACHE_E)
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  if (Sta.Dir.Dirty) then
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := src;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      NxtSta.Dir.InvSet[p] := false;
    end;
    NxtSta.Dir.HomeShrSet := false;
    NxtSta.Dir.HomeInvSet := false;
    NxtSta.UniMsg[src].Cmd := UNI_PutX;
    NxtSta.UniMsg[src].HomeProc := true;
    NxtSta.UniMsg[src].Data := Sta.HomeProc.CacheData;
    NxtSta.HomeProc.CacheState := CACHE_I;
    undefine NxtSta.HomeProc.CacheData;
  elsif (Sta.Dir.HeadVld ->
         Sta.Dir.HeadPtr = src  & !Sta.Dir.HomeShrSet &
         forall p : NODE do p != src -> !Sta.Dir.ShrSet[p] end) then
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := src;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      NxtSta.Dir.InvSet[p] := false;
    end;
    NxtSta.Dir.HomeShrSet := false;
    NxtSta.Dir.HomeInvSet := false;
    NxtSta.UniMsg[src].Cmd := UNI_PutX;
    NxtSta.UniMsg[src].HomeProc := true;
    NxtSta.UniMsg[src].Data := Sta.MemData;
    NxtSta.HomeProc.CacheState := CACHE_I;
    undefine NxtSta.HomeProc.CacheData;
    if (Sta.Dir.Local) then
      NxtSta.HomeProc.CacheState := CACHE_I;
      undefine NxtSta.HomeProc.CacheData;
      if (Sta.HomeProc.ProcCmd = NODE_Get) then
        NxtSta.HomeProc.InvMarked := true;
      end;
    end;
  else
    NxtSta.Dir.Pending := true;
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := src;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      if ( p != src &
           ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
             Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p ) ) then
        NxtSta.Dir.InvSet[p] := true;
        NxtSta.InvMsg[p].Cmd := INV_Inv;
      else
        NxtSta.Dir.InvSet[p] := false;
        NxtSta.InvMsg[p].Cmd := INV_None;
      end;
    end;
    NxtSta.Dir.HomeShrSet := false;
    NxtSta.Dir.HomeInvSet := false;
    NxtSta.HomeInvMsg.Cmd := INV_None;
    NxtSta.UniMsg[src].Cmd := UNI_PutX;
    NxtSta.UniMsg[src].HomeProc := true;
    NxtSta.UniMsg[src].Data := Sta.MemData;
    if (Sta.Dir.Local) then
      NxtSta.HomeProc.CacheState := CACHE_I;
      undefine NxtSta.HomeProc.CacheData;
      if (Sta.HomeProc.ProcCmd = NODE_Get) then
        NxtSta.HomeProc.InvMarked := true;
      end;
    end;
    NxtSta.PendReqSrc := src;
    NxtSta.PendReqCmd := UNI_GetX;
    NxtSta.Collecting := true;
    NxtSta.PrevData := Sta.CurrData;
    if (Sta.Dir.HeadPtr != src) then
      NxtSta.LastOtherInvAck := Sta.Dir.HeadPtr;
    else
      for p : NODE do
        if (p != src & Sta.Dir.ShrSet[p]) then NxtSta.LastOtherInvAck := p end;
      end;
    end;
  end;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_Nak"
  src != dst &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].Proc := dst;
  undefine NxtSta.UniMsg[src].Data;
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_Nak_Home"
  src != dst &
  Sta.HomeUniMsg.Cmd = UNI_GetX &
  Sta.HomeUniMsg.Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeUniMsg.Cmd := UNI_Nak;
  NxtSta.HomeUniMsg.Proc := dst;
  undefine NxtSta.HomeUniMsg.Data;
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_PutX"
  src != dst &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[dst].CacheState := CACHE_I;
  undefine NxtSta.Proc[dst].CacheData;
  NxtSta.UniMsg[src].Cmd := UNI_PutX;
  NxtSta.UniMsg[src].Proc := dst;
  NxtSta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  NxtSta.ShWbMsg.Cmd := SHWB_FAck;
  NxtSta.ShWbMsg.Proc := src;
  undefine NxtSta.ShWbMsg.Data;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_PutX_Home"
  src != dst &
  Sta.HomeUniMsg.Cmd = UNI_GetX &
  Sta.HomeUniMsg.Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.Proc[dst].CacheState := CACHE_I;
  undefine NxtSta.Proc[dst].CacheData;
  NxtSta.HomeUniMsg.Cmd := UNI_PutX;
  NxtSta.HomeUniMsg.Proc := dst;
  NxtSta.HomeUniMsg.Data := Sta.Proc[dst].CacheData;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
  Sta := NxtSta;
endrule;
endruleset;

rule "NI_Local_Put"
  Sta.HomeUniMsg.Cmd = UNI_Put
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeUniMsg.Cmd := UNI_None;
  undefine NxtSta.HomeUniMsg.Proc;
  undefine NxtSta.HomeUniMsg.Data;
  NxtSta.Dir.Pending := false;
  NxtSta.Dir.Dirty := false;
  NxtSta.Dir.Local := true;
  NxtSta.MemData := Sta.HomeUniMsg.Data;
  NxtSta.HomeProc.ProcCmd := NODE_None;
  if (Sta.HomeProc.InvMarked) then
    NxtSta.HomeProc.InvMarked := false;
    NxtSta.HomeProc.CacheState := CACHE_I;
    undefine NxtSta.HomeProc.CacheData;
  else
    NxtSta.HomeProc.CacheState := CACHE_S;
    NxtSta.HomeProc.CacheData := Sta.HomeUniMsg.Data;
  end;
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "NI_Remote_Put"
  Sta.UniMsg[dst].Cmd = UNI_Put
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.UniMsg[dst].Cmd := UNI_None;
  undefine NxtSta.UniMsg[dst].Proc;
  undefine NxtSta.UniMsg[dst].Data;
  NxtSta.Proc[dst].ProcCmd := NODE_None;
  if (Sta.Proc[dst].InvMarked) then
    NxtSta.Proc[dst].InvMarked := false;
    NxtSta.Proc[dst].CacheState := CACHE_I;
    undefine NxtSta.Proc[dst].CacheData;
  else
    NxtSta.Proc[dst].CacheState := CACHE_S;
    NxtSta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  end;
  Sta := NxtSta;
endrule;
endruleset;

rule "NI_Local_PutXAcksDone"
  Sta.HomeUniMsg.Cmd = UNI_PutX
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeUniMsg.Cmd := UNI_None;
  undefine NxtSta.HomeUniMsg.Proc;
  undefine NxtSta.HomeUniMsg.Data;
  NxtSta.Dir.Pending := false;
  NxtSta.Dir.Local := true;
  NxtSta.Dir.HeadVld := false;
  undefine NxtSta.Dir.HeadPtr;
  NxtSta.HomeProc.ProcCmd := NODE_None;
  NxtSta.HomeProc.InvMarked := false;
  NxtSta.HomeProc.CacheState := CACHE_E;
  NxtSta.HomeProc.CacheData := Sta.HomeUniMsg.Data;
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "NI_Remote_PutX"
  Sta.UniMsg[dst].Cmd = UNI_PutX &
  Sta.Proc[dst].ProcCmd = NODE_GetX
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.UniMsg[dst].Cmd := UNI_None;
  undefine NxtSta.UniMsg[dst].Proc;
  undefine NxtSta.UniMsg[dst].Data;
  NxtSta.Proc[dst].ProcCmd := NODE_None;
  NxtSta.Proc[dst].InvMarked := false;
  NxtSta.Proc[dst].CacheState := CACHE_E;
  NxtSta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  Sta := NxtSta;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Inv"
  Sta.InvMsg[dst].Cmd = INV_Inv
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.InvMsg[dst].Cmd := INV_InvAck;
  NxtSta.Proc[dst].CacheState := CACHE_I;
  undefine NxtSta.Proc[dst].CacheData;
  if (Sta.Proc[dst].ProcCmd = NODE_Get) then
    NxtSta.Proc[dst].InvMarked := true;
  end;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_InvAck"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending & Sta.Dir.InvSet[src]  
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.InvMsg[src].Cmd := INV_None;
  NxtSta.Dir.InvSet[src] := false;
  if (exists p : NODE do p != src & Sta.Dir.InvSet[p] end) then
    NxtSta.LastInvAck := src;
    for p : NODE do
      if (p != src & Sta.Dir.InvSet[p]) then
        NxtSta.LastOtherInvAck := p;
      end;
    end;
  else
    NxtSta.Dir.Pending := false;
    if (Sta.Dir.Local & !Sta.Dir.Dirty) then
      NxtSta.Dir.Local := false;
    end;
    NxtSta.Collecting := false;
    NxtSta.LastInvAck := src;
  end;
  Sta := NxtSta;
endrule;
endruleset;

rule "NI_Wb"
  Sta.WbMsg.Cmd = WB_Wb
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.WbMsg.Cmd := WB_None;
  undefine NxtSta.WbMsg.Proc;
  undefine NxtSta.WbMsg.Data;
  NxtSta.Dir.Dirty := false;
  NxtSta.Dir.HeadVld := false;
  undefine NxtSta.Dir.HeadPtr;
  NxtSta.MemData := Sta.WbMsg.Data;
  Sta := NxtSta;
endrule;

rule "NI_FAck"
  Sta.ShWbMsg.Cmd = SHWB_FAck
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.ShWbMsg.Cmd := SHWB_None;
  undefine NxtSta.ShWbMsg.Proc;
  undefine NxtSta.ShWbMsg.Data;
  NxtSta.Dir.Pending := false;
  if (Sta.Dir.Dirty) then
    NxtSta.Dir.HeadPtr := Sta.ShWbMsg.Proc;
  end;
  Sta := NxtSta;
endrule;

rule "NI_ShWb"
  Sta.ShWbMsg.Cmd = SHWB_ShWb
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.ShWbMsg.Cmd := SHWB_None;
  undefine NxtSta.ShWbMsg.Proc;
  undefine NxtSta.ShWbMsg.Data;
  NxtSta.Dir.Pending := false;
  NxtSta.Dir.Dirty := false;
  NxtSta.Dir.ShrVld := true;
  for p : NODE do
    NxtSta.Dir.ShrSet[p] := (p = Sta.ShWbMsg.Proc) | Sta.Dir.ShrSet[p];
    NxtSta.Dir.InvSet[p] := (p = Sta.ShWbMsg.Proc) | Sta.Dir.ShrSet[p];
  end;
  NxtSta.MemData := Sta.ShWbMsg.Data;
  Sta := NxtSta;
endrule;

ruleset src : NODE do
rule "NI_Replace"
  Sta.RpMsg[src].Cmd = RP_Replace
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.RpMsg[src].Cmd := RP_None;
  if (Sta.Dir.ShrVld) then
    NxtSta.Dir.ShrSet[src] := false;
    NxtSta.Dir.InvSet[src] := false;
  end;
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Replace"
  Sta.HomeRpMsg.Cmd = RP_Replace
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
  NxtSta.HomeRpMsg.Cmd := RP_None;
  if (Sta.Dir.ShrVld) then
    NxtSta.Dir.HomeShrSet := false;
    NxtSta.Dir.HomeInvSet := false;
  end;
  Sta := NxtSta;
endrule;
endruleset;


ruleset DATA_1 : DATA do
rule "n_ABS_Store_NODE_1"
Sta.Dir.Local = false &
		Sta.Dir.Dirty = true&
	forall NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.CurrData := DATA_1 ;
	NxtSta.LastWrVld := true ;
	NxtSta.LastWrPtr := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset DATA_1 : DATA do
rule "n_ABS_Store_Home_NODE_1"

	Sta.HomeProc.CacheState = CACHE_E
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeProc.CacheData := DATA_1 ;
	NxtSta.CurrData := DATA_1 ;
	NxtSta.LastWrVld := true ;
	NxtSta.LastWrPtr := Other ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_PI_Remote_Get_NODE_1"
Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.HomeProc := true ;
	Sta := NxtSta;
endrule;
rule "n_ABS_PI_Remote_Get_Home_NODE_1"

	Sta.HomeProc.ProcCmd = NODE_None &
	Sta.HomeProc.CacheState = CACHE_I
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeProc.ProcCmd := NODE_Get ;
	NxtSta.HomeUniMsg.Cmd := UNI_Get ;
	NxtSta.HomeUniMsg.HomeProc := true ;
	Sta := NxtSta;
endrule;
rule "n_ABS_PI_Remote_GetX_NODE_1"
Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_PI_Remote_GetX_Home_NODE_1"

	Sta.HomeProc.ProcCmd = NODE_None &
	Sta.HomeProc.CacheState = CACHE_I
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeProc.ProcCmd := NODE_GetX ;
	NxtSta.HomeUniMsg.Cmd := UNI_GetX ;
	NxtSta.HomeUniMsg.HomeProc := true ;
	Sta := NxtSta;
endrule;
rule "n_ABS_PI_Remote_PutX_NODE_1"
Sta.Dir.Local = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.Dirty = true&
	forall NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.WbMsg.Cmd := WB_Wb ;
	NxtSta.WbMsg.Proc := Other ;
	Sta := NxtSta;
endrule;
rule "n_ABS_PI_Remote_Replace_NODE_1"
Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Nak_NODE_1"

	True
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Nak_Home_NODE_1"

	Sta.HomeUniMsg.Cmd = UNI_Nak
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_None ;
	NxtSta.HomeProc.ProcCmd := NODE_None ;
	NxtSta.HomeProc.InvMarked := false ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Local_Get_Nak_NODE_1"

	 Sta.Dir.Pending |
    Sta.Dir.Dirty &
	Sta.Dir.Local &
	Sta.HomeProc.CacheState != CACHE_E |
    Sta.Dir.Dirty &
	!Sta.Dir.Local &
	Sta.Dir.HeadPtr = Other 
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Local_Get_Get_NODE_1"

	!Sta.Dir.Pending &
	Sta.Dir.Dirty &
	!Sta.Dir.Local &
	Sta.Dir.HeadPtr != Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.Dir.Pending := true ;
	NxtSta.PendReqSrc := Other ;
	NxtSta.PendReqCmd := UNI_Get ;
	NxtSta.Collecting := false ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Local_Get_Put_NODE_1"

	!Sta.Dir.Pending &
	Sta.Dir.Dirty -> Sta.Dir.Local &
	Sta.HomeProc.CacheState = CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	if (Sta.Dir.Dirty) then
    NxtSta.Dir.Dirty := false ;
	NxtSta.Dir.HeadVld := true ;
	NxtSta.Dir.HeadPtr := Other ;
	NxtSta.MemData := Sta.HomeProc.CacheData ;
	NxtSta.HomeProc.CacheState := CACHE_S ;
	else
    if (Sta.Dir.HeadVld) then
      NxtSta.Dir.ShrVld := true ;
	for p : NODE do
        NxtSta.Dir.InvSet[p] := (false) | Sta.Dir.ShrSet[p] ;
	NxtSta.Dir.HomeInvSet := (false) | Sta.Dir.HomeShrSet ;
	end ;
	else
      NxtSta.Dir.HeadVld := true ;
	NxtSta.Dir.HeadPtr := Other ;
	end ;
	end ;
	Sta := NxtSta;
endrule;

ruleset NODE_2 : NODE do
rule "n_ABS_NI_Remote_Get_Nak_NODE_1"

	Sta.Proc[NODE_2].CacheState != CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset NODE_1 : NODE do
rule "n_ABS_NI_Remote_Get_Nak_NODE_2"

	Sta.UniMsg[NODE_1].Cmd = UNI_Get &
	Sta.UniMsg[NODE_1].Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.UniMsg[NODE_1].Cmd := UNI_Nak ;
	NxtSta.UniMsg[NODE_1].Proc := Other ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := NODE_1 ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_NI_Remote_Get_Nak_NODE_1_NODE_2"

	Other != Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;

ruleset NODE_2 : NODE do
rule "n_ABS_NI_Remote_Get_Nak_Home_NODE_1"

	Sta.HomeUniMsg.Cmd = UNI_Get &
	Sta.HomeUniMsg.Proc = NODE_2 &
	Sta.Proc[NODE_2].CacheState != CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_Nak ;
	NxtSta.HomeUniMsg.Proc := NODE_2 ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset NODE_1 : NODE do
rule "n_ABS_NI_Remote_Get_Nak_Home_NODE_2"

	Sta.HomeUniMsg.Cmd = UNI_Get &
	Sta.HomeUniMsg.Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_Nak ;
	NxtSta.HomeUniMsg.Proc := Other ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := NODE_1 ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_NI_Remote_Get_Nak_Home_NODE_1_NODE_2"

	Other != Other &
	Sta.HomeUniMsg.Cmd = UNI_Get &
	Sta.HomeUniMsg.Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_Nak ;
	NxtSta.HomeUniMsg.Proc := Other ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;

ruleset NODE_2 : NODE do
rule "n_ABS_NI_Remote_Get_Put_NODE_1"

	Sta.Proc[NODE_2].CacheState = CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_1 : NODE do
		Sta.ShWbMsg.Proc != NODE_1
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.Proc[NODE_2].CacheState := CACHE_S ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset NODE_1 : NODE do
rule "n_ABS_NI_Remote_Get_Put_NODE_2"

	Sta.UniMsg[NODE_1].Cmd = UNI_Get &
	Sta.UniMsg[NODE_1].Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&Sta.ShWbMsg.Proc != NODE_1
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.UniMsg[NODE_1].Cmd := UNI_Put ;
	NxtSta.UniMsg[NODE_1].Proc := Other ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := NODE_1 ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_NI_Remote_Get_Put_NODE_1_NODE_2"

	Other != Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_1 : NODE do
		Sta.ShWbMsg.Proc != NODE_1
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;

ruleset NODE_2 : NODE do
rule "n_ABS_NI_Remote_Get_Put_Home_NODE_1"

	Sta.HomeUniMsg.Cmd = UNI_Get &
	Sta.HomeUniMsg.Proc = NODE_2 &
	Sta.Proc[NODE_2].CacheState = CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_1 : NODE do
		Sta.ShWbMsg.Proc != NODE_1
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.Proc[NODE_2].CacheState := CACHE_S ;
	NxtSta.HomeUniMsg.Cmd := UNI_Put ;
	NxtSta.HomeUniMsg.Proc := NODE_2 ;
	NxtSta.HomeUniMsg.Data := Sta.Proc[NODE_2].CacheData ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset NODE_1 : NODE do
rule "n_ABS_NI_Remote_Get_Put_Home_NODE_2"

	Sta.HomeUniMsg.Cmd = UNI_Get &
	Sta.HomeUniMsg.Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&Sta.ShWbMsg.Proc != NODE_1
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_Put ;
	NxtSta.HomeUniMsg.Proc := Other ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := NODE_1 ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_NI_Remote_Get_Put_Home_NODE_1_NODE_2"

	Other != Other &
	Sta.HomeUniMsg.Cmd = UNI_Get &
	Sta.HomeUniMsg.Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_1 : NODE do
		Sta.ShWbMsg.Proc != NODE_1
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_Put ;
	NxtSta.HomeUniMsg.Proc := Other ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Local_GetX_Nak_NODE_1"

	 Sta.Dir.Pending |
    Sta.Dir.Dirty &
	Sta.Dir.Local &
	Sta.HomeProc.CacheState != CACHE_E |
    Sta.Dir.Dirty &
	!Sta.Dir.Local &
	Sta.Dir.HeadPtr = Other 
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Local_GetX_GetX_NODE_1"

	!Sta.Dir.Pending &
	Sta.Dir.Dirty &
	!Sta.Dir.Local &
	Sta.Dir.HeadPtr != Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.Dir.Pending := true ;
	NxtSta.PendReqSrc := Other ;
	NxtSta.PendReqCmd := UNI_GetX ;
	NxtSta.Collecting := false ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Local_GetX_PutX_NODE_1"

	!Sta.Dir.Pending &
	Sta.Dir.Dirty -> Sta.Dir.Local &
	Sta.HomeProc.CacheState = CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	if (Sta.Dir.Dirty) then
    NxtSta.Dir.Local := false ;
	NxtSta.Dir.Dirty := true ;
	NxtSta.Dir.HeadVld := true ;
	NxtSta.Dir.HeadPtr := Other ;
	NxtSta.Dir.ShrVld := false ;
	for p : NODE do
      NxtSta.Dir.ShrSet[p] := false ;
	NxtSta.Dir.InvSet[p] := false ;
	end ;
	NxtSta.Dir.HomeShrSet := false ;
	NxtSta.Dir.HomeInvSet := false ;
	NxtSta.HomeProc.CacheState := CACHE_I ;
	elsif (Sta.Dir.HeadVld ->
         Sta.Dir.HeadPtr = Other  & !Sta.Dir.HomeShrSet &
         forall p : NODE do false -> !Sta.Dir.ShrSet[p] end) then
    NxtSta.Dir.Local := false ;
	NxtSta.Dir.Dirty := true ;
	NxtSta.Dir.HeadVld := true ;
	NxtSta.Dir.HeadPtr := Other ;
	NxtSta.Dir.ShrVld := false ;
	for p : NODE do
      NxtSta.Dir.ShrSet[p] := false ;
	NxtSta.Dir.InvSet[p] := false ;
	end ;
	NxtSta.Dir.HomeShrSet := false ;
	NxtSta.Dir.HomeInvSet := false ;
	NxtSta.HomeProc.CacheState := CACHE_I ;
	if (Sta.Dir.Local) then
      NxtSta.HomeProc.CacheState := CACHE_I ;
	if (Sta.HomeProc.ProcCmd = NODE_Get) then
        NxtSta.HomeProc.InvMarked := true ;
	end ;
	end ;
	else
    NxtSta.Dir.Pending := true ;
	NxtSta.Dir.Local := false ;
	NxtSta.Dir.Dirty := true ;
	NxtSta.Dir.HeadVld := true ;
	NxtSta.Dir.HeadPtr := Other ;
	NxtSta.Dir.ShrVld := false ;
	for p : NODE do
      NxtSta.Dir.ShrSet[p] := false ;
	if ( false &
           ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
             Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p ) ) then
        NxtSta.Dir.InvSet[p] := true ;
	NxtSta.InvMsg[p].Cmd := INV_Inv ;
	else
        NxtSta.Dir.InvSet[p] := false ;
	NxtSta.InvMsg[p].Cmd := INV_None ;
	end ;
	end ;
	NxtSta.Dir.HomeShrSet := false ;
	NxtSta.Dir.HomeInvSet := false ;
	NxtSta.HomeInvMsg.Cmd := INV_None ;
	if (Sta.Dir.Local) then
      NxtSta.HomeProc.CacheState := CACHE_I ;
	if (Sta.HomeProc.ProcCmd = NODE_Get) then
        NxtSta.HomeProc.InvMarked := true ;
	end ;
	end ;
	NxtSta.PendReqSrc := Other ;
	NxtSta.PendReqCmd := UNI_GetX ;
	NxtSta.Collecting := true ;
	NxtSta.PrevData := Sta.CurrData ;
	if (Sta.Dir.HeadPtr != Other) then
      NxtSta.LastOtherInvAck := Sta.Dir.HeadPtr ;
	else
      for p : NODE do
        if (false & Sta.Dir.ShrSet[p]) then NxtSta.LastOtherInvAck := p end ;
	end ;
	end ;
	end ;
	Sta := NxtSta;
endrule;

ruleset NODE_2 : NODE do
rule "n_ABS_NI_Remote_GetX_Nak_NODE_1"

	Sta.Proc[NODE_2].CacheState != CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset NODE_1 : NODE do
rule "n_ABS_NI_Remote_GetX_Nak_NODE_2"

	Sta.UniMsg[NODE_1].Cmd = UNI_GetX &
	Sta.UniMsg[NODE_1].Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.UniMsg[NODE_1].Cmd := UNI_Nak ;
	NxtSta.UniMsg[NODE_1].Proc := Other ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := NODE_1 ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_NI_Remote_GetX_Nak_NODE_1_NODE_2"

	Other != Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;

ruleset NODE_2 : NODE do
rule "n_ABS_NI_Remote_GetX_Nak_Home_NODE_1"

	Sta.HomeUniMsg.Cmd = UNI_GetX &
	Sta.HomeUniMsg.Proc = NODE_2 &
	Sta.Proc[NODE_2].CacheState != CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_Nak ;
	NxtSta.HomeUniMsg.Proc := NODE_2 ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset NODE_1 : NODE do
rule "n_ABS_NI_Remote_GetX_Nak_Home_NODE_2"

	Sta.HomeUniMsg.Cmd = UNI_GetX &
	Sta.HomeUniMsg.Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_Nak ;
	NxtSta.HomeUniMsg.Proc := Other ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := NODE_1 ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_NI_Remote_GetX_Nak_Home_NODE_1_NODE_2"

	Other != Other &
	Sta.HomeUniMsg.Cmd = UNI_GetX &
	Sta.HomeUniMsg.Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_Nak ;
	NxtSta.HomeUniMsg.Proc := Other ;
	NxtSta.NakcMsg.Cmd := NAKC_Nakc ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;

ruleset NODE_2 : NODE do
rule "n_ABS_NI_Remote_GetX_PutX_NODE_1"

	Sta.Proc[NODE_2].CacheState = CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_1 : NODE do
		Sta.ShWbMsg.Proc != NODE_1
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.Proc[NODE_2].CacheState := CACHE_I ;
	NxtSta.ShWbMsg.Cmd := SHWB_FAck ;
	NxtSta.ShWbMsg.Proc := Other ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset NODE_1 : NODE do
rule "n_ABS_NI_Remote_GetX_PutX_NODE_2"

	Sta.UniMsg[NODE_1].Cmd = UNI_GetX &
	Sta.UniMsg[NODE_1].Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&Sta.ShWbMsg.Proc != NODE_1
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.UniMsg[NODE_1].Cmd := UNI_PutX ;
	NxtSta.UniMsg[NODE_1].Proc := Other ;
	NxtSta.ShWbMsg.Cmd := SHWB_FAck ;
	NxtSta.ShWbMsg.Proc := NODE_1 ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := NODE_1 ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_NI_Remote_GetX_PutX_NODE_1_NODE_2"

	Other != Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_1 : NODE do
		Sta.ShWbMsg.Proc != NODE_1
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.ShWbMsg.Cmd := SHWB_FAck ;
	NxtSta.ShWbMsg.Proc := Other ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;

ruleset NODE_2 : NODE do
rule "n_ABS_NI_Remote_GetX_PutX_Home_NODE_1"

	Sta.HomeUniMsg.Cmd = UNI_GetX &
	Sta.HomeUniMsg.Proc = NODE_2 &
	Sta.Proc[NODE_2].CacheState = CACHE_E
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_1 : NODE do
		Sta.ShWbMsg.Proc != NODE_1
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.Proc[NODE_2].CacheState := CACHE_I ;
	NxtSta.HomeUniMsg.Cmd := UNI_PutX ;
	NxtSta.HomeUniMsg.Proc := NODE_2 ;
	NxtSta.HomeUniMsg.Data := Sta.Proc[NODE_2].CacheData ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
endruleset;



ruleset NODE_1 : NODE do
rule "n_ABS_NI_Remote_GetX_PutX_Home_NODE_2"

	Sta.HomeUniMsg.Cmd = UNI_GetX &
	Sta.HomeUniMsg.Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&Sta.ShWbMsg.Proc != NODE_1
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_PutX ;
	NxtSta.HomeUniMsg.Proc := Other ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := NODE_1 ;
	Sta := NxtSta;
endrule;
endruleset;


rule "n_ABS_NI_Remote_GetX_PutX_Home_NODE_1_NODE_2"

	Other != Other &
	Sta.HomeUniMsg.Cmd = UNI_GetX &
	Sta.HomeUniMsg.Proc = Other
 	& Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.HeadVld = true &
		Sta.Dir.ShrVld = false &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_1 : NODE do
		Sta.ShWbMsg.Proc != NODE_1
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeUniMsg.Cmd := UNI_PutX ;
	NxtSta.HomeUniMsg.Proc := Other ;
	NxtSta.FwdCmd := UNI_None ;
	NxtSta.FwdSrc := Other ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Remote_Put_NODE_1"

	True
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Remote_PutX_NODE_1"
Sta.Dir.Local = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadVld = true &
		Sta.Dir.Dirty = true &
		Sta.WbMsg.Cmd != WB_Wb&
	forall NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.ShWbMsg.Proc != NODE_2
	end
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Inv_NODE_1"

	True
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_InvAck_NODE_1"

	Sta.Dir.Pending
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	if (exists p : NODE do false & Sta.Dir.InvSet[p] end) then
    NxtSta.LastInvAck := Other ;
	for p : NODE do
      if (false & Sta.Dir.InvSet[p]) then
        NxtSta.LastOtherInvAck := p ;
	end ;
	end ;
	else
    NxtSta.Dir.Pending := false ;
	if (Sta.Dir.Local & !Sta.Dir.Dirty) then
      NxtSta.Dir.Local := false ;
	end ;
	NxtSta.Collecting := false ;
	NxtSta.LastInvAck := Other ;
	end ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Replace_NODE_1"

	True
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	Sta := NxtSta;
endrule;
rule "n_ABS_NI_Replace_NODE_1"

	Sta.HomeRpMsg.Cmd = RP_Replace
==>
 var NxtSta : STATE; 
begin
	NxtSta := Sta ;
	NxtSta.HomeRpMsg.Cmd := RP_None ;
	if (Sta.Dir.ShrVld) then
    NxtSta.Dir.HomeShrSet := false ;
	NxtSta.Dir.HomeInvSet := false ;
	end ;
	Sta := NxtSta;
endrule;

ruleset i : NODE do
Invariant "rule_1"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadVld = true);
endruleset;
