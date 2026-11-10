# Correspondencia matemática de la etapa 17

Se inventarió el capítulo III completo con el PDF del ZIP de conectores como fuente normativa. La [matriz](INVENTARIO_FORMAL_CAPITULO_III.md) distingue enunciados, ecuaciones, definiciones y construcciones. El [estado central](ESTADO_FORMALIZACION_CAPITULO_III.md) y el [mapa](MAPA_VERIFICACION.md) enlazan esa clasificación con la pila previa.

## Proposición 3.10, pp. 75–77

| Paso de la tesis | Declaración en `TesisPINN/ComparadoresAproximados.lean` | Correspondencia |
|---|---|---|
| (3.38), aproximación aditiva del ínfimo en la clase | `ProblemaPINN.minimizadorAproximado_iff_le_infimo` | Equivalencia con la comparación contra todo candidato admisible. La clase es no vacía porque contiene al candidato, y el objetivo está acotado inferiormente por cero. |
| (3.39)–(3.40), control de la regularidad y del objetivo | `ProblemaPINN.cotas_minimizador_aproximado` | De una comparación con (v), de $E_m(v)\le\varepsilon$ y $R(v)\le R^*$ se deduce $R(h)\le R^*+(\varepsilon+\delta)/a$ y $J_m(h)\le a(R^*+(\varepsilon+\delta)/a)$, con los dos pesos iguales a (a>0). |
| (3.41), transferencia a población | `perdidaPoblacional_aproximada_bajo_cobertura` | La cota de (3.13) se demuestra desde la cobertura y se compara cada peso mínimo con el peso igual. Los dos términos de datos se conservan con los radios explícitos. Sustituir los radios (3.5) y acotar sus constantes por el máximo (3.9) produce la forma impresa para (d=2). |

La prueba variacional es puntual y no requiere hipótesis geométricas. La parte poblacional reutiliza la geometría con exponentes de masa 2 y 1, residuos escalares, medidas concentradas e integrabilidad explícita. Esta última se puede suministrar con `poblacionIntegrable_de_holder_acotado` cuando se instancie la familia aleatoria. El término de datos de Lean utiliza cotas Hölder válidas. La identificación con el funcional literal de la tesis requiere elegir las seminormas exactas para regularizar cada operador. La prueba no presupone que la pérdida empírica del comparador sea cero y deja explícita la tolerancia del optimizador.

La división de (3.39) utiliza (a>0). La cota de (3.41) usa (C_m>0), demostrado a partir del número positivo de muestras interiores, la constante de masa y el radio. En los lemas puntuales, la pérdida no negativa del comparador implica que su cota empírica no es negativa. La comparación del candidato consigo mismo implica que la tolerancia de optimización no es negativa. Por eso no son premisas independientes de esos lemas.

## Alcance y verificación

La etapa formaliza la parte determinista de P3.10. La selección mensurable, la condición eventual de tolerancias y la aplicación de Borel–Cantelli para (3.43) permanecen como pasos de integración. La geometría de dimensión general y la transferencia uniforme para subóptimos se registran por separado en la matriz. No se detectó un error sustantivo en las desigualdades comprobadas de P3.10.

`lake build` terminó correctamente con 3 229 tareas en el entorno fijado. Los tres `#check` confirmaron las firmas. Los tres `#print axioms` registraron solo `propext`, `Classical.choice` y `Quot.sound`. La búsqueda en las fuentes propias quedó libre de `sorry`, `admit`, `sorryAx` y declaraciones `axiom`. El PDF, los módulos de prueba previos y las versiones fijadas se conservan.
