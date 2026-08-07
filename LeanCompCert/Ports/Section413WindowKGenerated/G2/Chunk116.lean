import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk116

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360783089605409318, 360783090348095375⟩, ⟨(-2300027277919484074), (-2300021440421354390)⟩, true⟩

def state01 : KState := ⟨⟨360649472305146878, 360649473049183750⟩, ⟨(-749925553208110621), (-749919700033855753)⟩, true⟩

def words00 : List Nat := [360584843034280803, 360584848974138694, 360584859046667903, 360584869117502321, 360584874138849885, 360584879496117900, 360584880449335800, 360584881402404928, 360584881402520633, 360584886045477450]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360474215378726292, 360474216124101439⟩, ⟨1285701999594670019, 1285707868313115955⟩, true⟩

def words01 : List Nat := [360584894016357341, 360584901985891185, 360584904224815214, 360584904224957167, 360584899115373626, 360584889466305517, 360584879818856486, 360584877529043940, 360584871762846424, 360584862240135270]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360530294319510956, 360530295066226877⟩, ⟨634302649660401636, 634308533965191078⟩, true⟩

def words02 : List Nat := [360584852719028726, 360584853344113155, 360584860694805199, 360584868044259622, 360584869280555919, 360584869280697998, 360584863181972122, 360584852804888062, 360584842429545506, 360584835782818897]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360619479800443789, 360619480548513060⟩, ⟨(-403498064708352625), (-403492164657314835)⟩, true⟩

def words03 : List Nat := [360584831093691292, 360584822705374241, 360584814318472343, 360584817910924475, 360584818323332132, 360584818735691544, 360584818735819542, 360584815315369229, 360584816273037072, 360584819250973561]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360470539729383918, 360470540478795583⟩, ⟨1330585161034859249, 1330591076718248709⟩, true⟩

def words04 : List Nat := [360584822031758254, 360584822031900561, 360584817495483859, 360584809271355171, 360584801048616109, 360584788083470950, 360584778824239476, 360584772559897754, 360584766296613861, 360584754305123330]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360601682158637219, 360601682909392556⟩, ⟨(-198221562859228987), (-198215631515416315)⟩, true⟩

def words05 : List Nat := [360584744502318290, 360584739287459493, 360584734073454538, 360584733109305792, 360584724841112288, 360584709169895850, 360584693501340958, 360584685138337150, 360584683283899823, 360584684741867008]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606990013545895, 360606990765659976⟩, ⟨(-260399930463191031), (-260393983269685415)⟩, true⟩

def words06 : List Nat := [360584684741994795, 360584680803936041, 360584684096077341, 360584688321920661, 360584690636702337, 360584690636845216, 360584690190089200, 360584686072084436, 360584681954760360, 360584679568395844]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360468567317931616, 360468568071388973⟩, ⟨1355960790474655810, 1355966753351047248⟩, true⟩

def words07 : List Nat := [360584682520904111, 360584685472932903, 360584685473061207, 360584684706697170, 360584682039021182, 360584677474964399, 360584675621369769, 360584675621512475, 360584671055516638, 360584661115340262]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586808986029436, 360586809740837059⟩, ⟨(-25658995696047348), (-25653017041989032)⟩, true⟩

def words08 : List Nat := [360584651176833859, 360584651978296116, 360584655272118558, 360584658565402632, 360584658565534572, 360584655346645151, 360584644860346673, 360584632584672269, 360584620311056857, 360584615487390649]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360508344483463219, 360508345239633306⟩, ⟨891926168923883773, 891932163511808003⟩, true⟩

def words09 : List Nat := [360584615487519322, 360584611897152590, 360584608307373495, 360584606957702794, 360584606957822574, 360584606254714376, 360584605551712611, 360584599040027753, 360584585273959364, 360584578757882179]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk116
