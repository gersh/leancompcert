import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk022

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨359206063556680520, 359206063578974424⟩, ⟨2977018270295678242, 2977018303655212604⟩, true⟩

def state01 : KState := ⟨⟨360304956815341069, 360304956837849983⟩, ⟨552866273732706826, 552866307566330746⟩, true⟩

def words00 : List Nat := [360558638910049387, 360558108545852320, 360557686736771389, 360557466306047428, 360557246075259342, 360556831600429226, 360556217277879134, 360555803965750614, 360555391027823073, 360555122587879997]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨359833647251353502, 359833647274080472⟩, ⟨1598372558413129849, 1598372592729753309⟩, true⟩

def words01 : List Nat := [360555009441925810, 360554727569085225, 360554445950982773, 360554408557018994, 360554408557038210, 360554397648077816, 360554386748956192, 360554272369298334, 360553959393355846, 360553634928463244]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360184121902945728, 360184121925889162⟩, ⟨819312351481880701, 819312386280146805⟩, true⟩

def words02 : List Nat := [360553310755742429, 360553184852571379, 360553059825734221, 360552794701830012, 360552529816235790, 360552194476430327, 360552018413829594, 360551888143551533, 360551757990157777, 360551526583413892]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360272251667488858, 360272251690650827⟩, ⟨618463900098675933, 618463935385389931⟩, true⟩

def words03 : List Nat := [360551361901829087, 360551255191449614, 360551148576639612, 360550900701748633, 360550457217277408, 360549837058601094, 360549217454376058, 360548793517590657, 360548474975747279, 360548351661805019]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨359954635823190102, 359954635846573389⟩, ⟨1330031567788552251, 1330031603572116513⟩, true⟩

def words04 : List Nat := [360548228457911949, 360548000154740179, 360547732837399794, 360547660184587070, 360547587596492292, 360547460794545480, 360547140601091628, 360546665969444135, 360546191759874790, 360545761003716552]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359439885061801383, 359439885085404467⟩, ⟨2494135577542757443, 2494135613821990773⟩, true⟩

def words05 : List Nat := [360545498398157020, 360545429054774926, 360545359772946851, 360545190689801618, 360545081578545746, 360544816291350685, 360544551239228521, 360544358159763783, 360543973449179329, 360543484914529242]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360278000772287529, 360278000796112962⟩, ⟨592701279324881545, 592701316107715065⟩, true⟩

def words06 : List Nat := [360542996812014800, 360542386439156431, 360541913003299302, 360541524022009653, 360541135384189555, 360540577632257683, 360540017926982595, 360539649114050323, 360539280626199274, 360539102697482000]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360104842730845555, 360104842754895732⟩, ⟨987027890784340578, 987027928078470026⟩, true⟩

def words07 : List Nat := [360538987725287559, 360538774064232213, 360538560591171657, 360538614705169437, 360538614705189687, 360538532720153820, 360538450807127220, 360538208416565881, 360537939695666801, 360537749740895061]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360712343445331537, 360712343469605220⟩, ⟨(-400118825817728776), (-400118788012859592)⟩, true⟩

def words08 : List Nat := [360537559952669657, 360537580136967393, 360537580136988519, 360537504586049081, 360537429101233612, 360537301254325920, 360537439552698722, 360537602172848177, 360537619108003012, 360537695373571672]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361326695459023540, 361326695483521968⟩, ⟨(-1809834370716271318), (-1809834332395603252)⟩, true⟩

def words09 : List Nat := [360537842417234385, 360537989332649475, 360538322462417475, 360538604320333666, 360538703108157622, 360538801809968932, 360539086285124418, 360539468718625410, 360539810991151392, 360540152966183592]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk022
