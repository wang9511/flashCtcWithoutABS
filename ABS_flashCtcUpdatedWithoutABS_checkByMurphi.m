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


ruleset j : NODE do
Invariant "rule_9"
	(Sta.Proc[j].ProcCmd != NODE_GetX -> Sta.UniMsg[j].Cmd != UNI_GetX);
endruleset;


ruleset j : NODE do
Invariant "rule_19"
	(Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_GetX);
endruleset;


ruleset j : NODE do
Invariant "rule_33"
	(Sta.Proc[j].ProcCmd = NODE_Get -> Sta.UniMsg[j].Cmd != UNI_GetX);
endruleset;


ruleset j : NODE do
Invariant "rule_36"
	(Sta.UniMsg[j].Cmd != UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_38"
	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset j : NODE do
Invariant "rule_40"
	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
Invariant "rule_44"
	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd = NODE_GetX);
endruleset;


ruleset j : NODE do
Invariant "rule_49"
	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
Invariant "rule_55"
	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd != NODE_None);
endruleset;


ruleset j : NODE do
Invariant "rule_68"
	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd != NODE_Get);
endruleset;


ruleset j : NODE do
Invariant "rule_69"
	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
Invariant "rule_71"
	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_79"
	(Sta.Dir.HeadPtr = i -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_95"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_124"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_125"
	(Sta.Dir.InvSet[i] = false -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_131"
	(Sta.Dir.Pending = false -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_166"
	(Sta.InvMsg[i].Cmd != INV_Inv -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_187"
	(Sta.Proc[j].ProcCmd = NODE_GetX -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset j : NODE do
Invariant "rule_216"
	(Sta.Proc[j].ProcCmd = NODE_None -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset j : NODE do
Invariant "rule_256"
	(Sta.Proc[j].ProcCmd != NODE_Get -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset j : NODE do
Invariant "rule_262"
	(Sta.Proc[j].InvMarked = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_356"
	(Sta.RpMsg[j].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_373"
	(Sta.Proc[j].ProcCmd = NODE_GetX -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
Invariant "rule_384"
	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
Invariant "rule_399"
	(Sta.Proc[j].ProcCmd != NODE_None -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
Invariant "rule_441"
	(Sta.Proc[j].ProcCmd = NODE_Get -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
Invariant "rule_445"
	(Sta.Proc[j].CacheState != CACHE_S -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_476"
	(Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
Invariant "rule_482"
	(Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_497"
	(Sta.Dir.HeadPtr = i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
Invariant "rule_515"
	(Sta.Dir.HeadPtr = i -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
Invariant "rule_518"
	(Sta.Dir.HeadPtr = i -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_521"
	(Sta.Dir.HeadPtr = i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_525"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Local = false);
endruleset;


ruleset i : NODE do
Invariant "rule_536"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.Local = false);
endruleset;
Invariant "rule_555"
	(Sta.Dir.Local = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
Invariant "rule_558"
	(Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb);


ruleset i : NODE do
Invariant "rule_559"
	(Sta.Dir.Local = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
Invariant "rule_560"
	(Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);


ruleset i : NODE do
Invariant "rule_566"
	(Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
Invariant "rule_569"
	(Sta.Dir.Local = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
Invariant "rule_571"
	(Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
Invariant "rule_572"
	(Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
Invariant "rule_582"
	(Sta.Dir.Local = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);


ruleset j : NODE do
Invariant "rule_585"
	(Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;
Invariant "rule_587"
	(Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
Invariant "rule_590"
	(Sta.Dir.Dirty = false -> Sta.WbMsg.Cmd != WB_Wb);


ruleset i : NODE do
Invariant "rule_591"
	(Sta.Dir.Dirty = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_601"
	(Sta.Dir.Dirty = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
Invariant "rule_604"
	(Sta.Dir.Dirty = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
Invariant "rule_611"
	(Sta.Dir.Dirty = false -> Sta.MemData = Sta.CurrData);


ruleset j : NODE do
Invariant "rule_618"
	(Sta.Dir.Dirty = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;
Invariant "rule_620"
	(Sta.Dir.Dirty = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);


ruleset j : NODE do
Invariant "rule_621"
	(Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_624"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE do
Invariant "rule_631"
	(Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_635"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.Dirty = true);
endruleset;
Invariant "rule_640"
	(Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false);
Invariant "rule_645"
	(Sta.MemData != Sta.CurrData -> Sta.Dir.Dirty = true);
Invariant "rule_655"
	(Sta.Dir.Dirty = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);


ruleset j : NODE do
Invariant "rule_659"
	(Sta.Dir.InvSet[j] = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_665"
		(i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_694"
		(i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_702"
	(Sta.Dir.Pending = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_705"
	(Sta.Dir.ShrVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_717"
	(Sta.MemData != Sta.CurrData -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_723"
	(Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_738"
	(Sta.Dir.ShrSet[j] = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_742"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_745"
	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_750"
	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_753"
	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_760"
	(Sta.Proc[i].ProcCmd != NODE_GetX -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_767"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_769"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_772"
	(Sta.UniMsg[i].Cmd != UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_775"
	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_782"
	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset i : NODE do
Invariant "rule_785"
	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_792"
	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd = NODE_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_795"
	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
Invariant "rule_796"
	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
Invariant "rule_799"
	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
Invariant "rule_803"
	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_822"
	(Sta.Dir.InvSet[j] = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_858"
	(Sta.Dir.InvSet[j] = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_883"
	(Sta.Dir.InvSet[j] = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_887"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
Invariant "rule_916"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
Invariant "rule_945"
	(Sta.Dir.HeadVld = false -> Sta.WbMsg.Cmd != WB_Wb);
Invariant "rule_960"
	(Sta.WbMsg.Cmd != WB_Wb -> Sta.ShWbMsg.Cmd != SHWB_ShWb);


ruleset j : NODE do
Invariant "rule_966"
	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd != NODE_GetX);
endruleset;


ruleset j : NODE do
Invariant "rule_975"
	(Sta.Proc[j].ProcCmd != NODE_GetX -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
Invariant "rule_990"
	(Sta.Proc[j].ProcCmd != NODE_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_993"
	(Sta.Proc[j].ProcCmd = NODE_GetX -> Sta.UniMsg[j].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
Invariant "rule_995"
	(Sta.Proc[j].ProcCmd = NODE_GetX -> Sta.UniMsg[j].Cmd != UNI_Get);
endruleset;


ruleset j : NODE do
Invariant "rule_996"
	(Sta.Proc[j].ProcCmd = NODE_GetX -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
Invariant "rule_1016"
	(Sta.Proc[j].ProcCmd = NODE_GetX -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
Invariant "rule_1018"
	(Sta.Proc[j].ProcCmd = NODE_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1021"
	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1027"
	(Sta.Proc[i].ProcCmd != NODE_None -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1030"
	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1033"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1038"
	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1040"
	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1047"
	(Sta.Dir.HeadVld = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1053"
	(Sta.Proc[i].CacheState != CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1056"
		(i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Proc != j);
endruleset;


ruleset i : NODE do
Invariant "rule_1060"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1061"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
Invariant "rule_1064"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1067"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1068"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1069"
		(i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1070"
		(i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1072"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1073"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1074"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_1075"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE do
Invariant "rule_1078"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1080"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
Invariant "rule_1081"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
Invariant "rule_1083"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_1084"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheData = Sta.CurrData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1087"
		(i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1089"
	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1106"
	(Sta.ShWbMsg.Cmd != SHWB_FAck -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
Invariant "rule_1120"
	(Sta.ShWbMsg.Cmd != SHWB_FAck -> Sta.ShWbMsg.Proc != j);
endruleset;
Invariant "rule_1123"
	(Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);


ruleset j : NODE do
Invariant "rule_1180"
	(Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
Invariant "rule_1216"
	(Sta.Proc[j].ProcCmd != NODE_Get -> Sta.UniMsg[j].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
Invariant "rule_1223"
	(Sta.UniMsg[j].Cmd != UNI_Put -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1228"
	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset i : NODE do
Invariant "rule_1234"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[i].Data = Sta.CurrData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1236"
		(i != j) ->	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
Invariant "rule_1239"
	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1242"
	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE do
Invariant "rule_1247"
	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
Invariant "rule_1250"
	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
Invariant "rule_1254"
	(Sta.UniMsg[i].Data = Sta.CurrData -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1264"
		(i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1309"
		(i != j) ->	(Sta.Proc[i].CacheState != CACHE_I -> Sta.UniMsg[i].Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1313"
		(i != j) ->	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.UniMsg[i].Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1320"
		(i != j) ->	(Sta.UniMsg[i].Proc != j -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1328"
	(Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Get);
endruleset;


ruleset j : NODE do
Invariant "rule_1343"
	(Sta.Proc[j].ProcCmd != NODE_Get -> Sta.UniMsg[j].Cmd != UNI_Get);
endruleset;


ruleset j : NODE do
Invariant "rule_1346"
	(Sta.UniMsg[j].Cmd != UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1347"
	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
Invariant "rule_1353"
	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd != NODE_None);
endruleset;


ruleset j : NODE do
Invariant "rule_1366"
	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd = NODE_Get);
endruleset;


ruleset j : NODE do
Invariant "rule_1368"
	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
Invariant "rule_1370"
	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1385"
	(Sta.Proc[j].ProcCmd != NODE_None -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
Invariant "rule_1427"
	(Sta.Proc[j].ProcCmd = NODE_Get -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
Invariant "rule_1431"
	(Sta.Proc[j].CacheState = CACHE_I -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1454"
	(Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_1490"
	(Sta.InvMsg[j].Cmd != INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1504"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1505"
	(Sta.Dir.InvSet[i] = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1512"
	(Sta.Dir.Pending = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1515"
	(Sta.Dir.ShrVld = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1527"
	(Sta.MemData != Sta.CurrData -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1533"
	(Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1548"
	(Sta.Dir.ShrSet[i] = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1553"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset i : NODE do
Invariant "rule_1558"
	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset i : NODE do
Invariant "rule_1565"
	(Sta.Proc[i].ProcCmd != NODE_None -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
Invariant "rule_1567"
	(Sta.Proc[i].ProcCmd != NODE_None -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
Invariant "rule_1571"
	(Sta.Proc[i].ProcCmd != NODE_None -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1575"
	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1580"
	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1582"
	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE do
Invariant "rule_1585"
	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1586"
	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
Invariant "rule_1589"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.Proc[i].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
Invariant "rule_1591"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.Proc[i].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
Invariant "rule_1594"
	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1609"
	(Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
Invariant "rule_1646"
	(Sta.ShWbMsg.Proc != i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE ; i : NODE do
Invariant "rule_1653"
		(j != i) ->	(Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
Invariant "rule_1700"
		(j != i) ->	(Sta.UniMsg[j].Proc != i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1702"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1708"
	(Sta.Proc[i].ProcCmd != NODE_Get -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1713"
	(Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1714"
	(Sta.Proc[i].ProcCmd != NODE_Get -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
Invariant "rule_1718"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1720"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1723"
	(Sta.Proc[i].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1725"
	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1730"
	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd = NODE_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_1738"
	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
Invariant "rule_1741"
	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
Invariant "rule_1745"
	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1793"
	(Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1809"
	(Sta.Proc[j].ProcCmd != NODE_None -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
Invariant "rule_1811"
	(Sta.Proc[j].ProcCmd != NODE_None -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1814"
	(Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
Invariant "rule_1818"
	(Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Nak);
endruleset;


ruleset j : NODE do
Invariant "rule_1829"
	(Sta.Proc[j].ProcCmd = NODE_None -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1835"
	(Sta.Proc[i].ProcCmd != NODE_GetX -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1840"
	(Sta.Dir.HeadVld = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1842"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1844"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1847"
	(Sta.UniMsg[i].Cmd != UNI_PutX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1848"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1849"
		(i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1850"
		(i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
Invariant "rule_1852"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1853"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].ProcCmd = NODE_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_1856"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1857"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
Invariant "rule_1858"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
Invariant "rule_1860"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
Invariant "rule_1861"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1862"
		(i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
Invariant "rule_1864"
	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_1897"
	(Sta.Dir.InvSet[i] = false -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_1906"
	(Sta.Dir.InvSet[i] = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1910"
	(Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1936"
		(i != j) ->	(Sta.Proc[i].CacheState != CACHE_I -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1940"
		(i != j) ->	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
Invariant "rule_1947"
	(Sta.ShWbMsg.Proc != j -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1969"
	(Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
Invariant "rule_1979"
	(Sta.Proc[j].ProcCmd = NODE_Get -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
Invariant "rule_1984"
	(Sta.UniMsg[j].Cmd != UNI_PutX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_1991"
	(Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;
Invariant "rule_1997"
	(Sta.Dir.Pending = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);


ruleset i : NODE do
Invariant "rule_1999"
	(Sta.Dir.Pending = false -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;
Invariant "rule_2004"
	(Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
Invariant "rule_2006"
	(Sta.Dir.Pending = true -> Sta.Dir.ShrVld = false);
Invariant "rule_2022"
	(Sta.Dir.Pending = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);


ruleset i : NODE do
Invariant "rule_2024"
	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_2031"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_2033"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE do
Invariant "rule_2036"
	(Sta.UniMsg[i].Cmd != UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_2038"
	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_2042"
	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
Invariant "rule_2045"
	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
Invariant "rule_2049"
	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
Invariant "rule_2060"
	(Sta.MemData != Sta.CurrData -> Sta.Dir.ShrVld = false);
Invariant "rule_2066"
	(Sta.Dir.HeadVld = false -> Sta.Dir.ShrVld = false);
Invariant "rule_2081"
	(Sta.Dir.ShrVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);


ruleset i : NODE do
Invariant "rule_2090"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_2092"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE do
Invariant "rule_2095"
	(Sta.Proc[i].ProcCmd != NODE_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_2099"
	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
Invariant "rule_2100"
	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
Invariant "rule_2101"
	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
Invariant "rule_2103"
	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
Invariant "rule_2107"
	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_2122"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE do
Invariant "rule_2126"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE do
Invariant "rule_2133"
	(Sta.UniMsg[i].Cmd != UNI_Nak -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_2160"
	(Sta.UniMsg[j].Cmd != UNI_Nak -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_2186"
	(Sta.InvMsg[j].Cmd != INV_Inv -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_2197"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
Invariant "rule_2201"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
Invariant "rule_2208"
	(Sta.Proc[i].InvMarked = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
Invariant "rule_2217"
	(Sta.MemData != Sta.CurrData -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
Invariant "rule_2226"
	(Sta.MemData = Sta.CurrData -> Sta.ShWbMsg.Cmd != SHWB_ShWb);


ruleset i : NODE do
Invariant "rule_2233"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
Invariant "rule_2237"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
Invariant "rule_2244"
	(Sta.UniMsg[i].Cmd != UNI_Put -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_2259"
	(Sta.Proc[i].CacheState != CACHE_S -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_2264"
	(Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
Invariant "rule_2265"
	(Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != j);
endruleset;
Invariant "rule_2266"
	(Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
Invariant "rule_2273"
	(Sta.Dir.HeadVld = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
Invariant "rule_2285"
	(Sta.NakcMsg.Cmd != NAKC_Nakc -> Sta.ShWbMsg.Cmd != SHWB_ShWb);


ruleset i : NODE do
Invariant "rule_2287"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_2289"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.Proc[i].CacheState != CACHE_I);
endruleset;


ruleset i : NODE do
Invariant "rule_2293"
	(Sta.Proc[i].CacheState != CACHE_I -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_2298"
	(Sta.Proc[i].CacheState = CACHE_I -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_2299"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_2306"
	(Sta.InvMsg[i].Cmd != INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
Invariant "rule_2311"
	(Sta.Proc[i].CacheData = Sta.CurrData -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_2314"
	(Sta.Proc[j].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_2315"
	(Sta.Proc[j].ProcCmd = NODE_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
Invariant "rule_2317"
	(Sta.Proc[j].ProcCmd = NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_2320"
	(Sta.Proc[j].CacheState != CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
Invariant "rule_2322"
	(Sta.Dir.HeadPtr != j -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
