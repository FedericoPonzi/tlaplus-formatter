---------------------- MODULE HourClock ----------------------

EXTENDS Naturals, TLC

VARIABLE
         hr

HCini ==
         hr \in ( 1 .. 12 ) 

HCnxt ==
         hr' = IF
              hr # 12 
         THEN
              hr + 1 
         ELSE
              1 

HC ==
      HCini /\ [] [ HCnxt ]_ hr 


--------------------------------------------------------------

THEOREM HC => [] HCini ==============================================================
