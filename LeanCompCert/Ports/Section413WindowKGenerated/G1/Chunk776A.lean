import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk776A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499874614615603, 362499964700625066⟩, ⟨(-1149997493997677529), (-1145276789651763695)⟩, true⟩

def state01 : KState := ⟨⟨362486894263801374, 362486984373974229⟩, ⟨(-142653739038086808), (-137931159489854768)⟩, true⟩

def words00 : List Nat := [371285206361533223, 371285206444058684, 371285206671975126, 371285206901247195, 371285207111664820, 371285207114342105, 371285207103667433, 371285207092939665, 371285207136534911, 371285207162503048]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481527101296994, 362481617235562606⟩, ⟨273973668311781373, 278698117816101403⟩, true⟩

def words01 : List Nat := [371285207353114848, 371285207544787293, 371285207720069893, 371285207722747708, 371285207693372405, 371285207697339025, 371285207865652063, 371285207868329863, 371285207824030234, 371285207780754775]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486801842346475, 362486892000597017⟩, ⟨(-135454659245793016), (-130728347907602358)⟩, true⟩

def words02 : List Nat := [371285207855922987, 371285207910945706, 371285208004187588, 371285208098502628, 371285208152408976, 371285208155088457, 371285208016659602, 371285207965667810, 371285208005145598, 371285208029658763]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489102226732139, 362489192409408589⟩, ⟨(-314026964989724599), (-309298757343542649)⟩, true⟩

def words03 : List Nat := [371285208048803365, 371285208068890476, 371285208210796689, 371285208290932162, 371285208420720650, 371285208551521298, 371285208648867576, 371285208651564295, 371285208650819286, 371285208705471964]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484461662371177, 362484551868897501⟩, ⟨46316908698141612, 51046968172704412⟩, true⟩

def words04 : List Nat := [371285208924372610, 371285208927051224, 371285208925144893, 371285208923269045, 371285208959149636, 371285208962101593, 371285209041434029, 371285209166014364, 371285209264294400, 371285209267071007]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk776A
