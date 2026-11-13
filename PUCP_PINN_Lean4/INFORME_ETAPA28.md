# Etapa 28 · Operador de traza por caras del cuadrado

Base en la [PR #29](https://github.com/MichaelMobius/tesispucp/pull/29), commit `09a0852e926392bc0f8146ca0105624c9cb486db`. El enunciado de C3.23 se cotejó en la página impresa 109 del PDF normativo. Para (3.81)–(3.82) exige igual traza de dos elementos arbitrarios de $H^1(U)$ y laplaciano residual en $L^2(U)$, con $U=(-1,1)^2$, $e=h-u^*$ y $\Delta u^*=f$. La aplicación de (3.83) usa las hipótesis de P3.15 con $\alpha=1/2$.

## Construcción

El espacio `H1Graph` es el par ambiental de clases $L^2$ de valor y campo vectorial. Su subespacio `W12` exige que el campo sea el gradiente débil de la función. Esta identificación viene de `mem_W12_iff_hasWeakFDerivOn` de EllipticPDE. El dominio del operador es el subtipo `W12`.

Con $I=(-1,1)$, los pesos $p_+(t)=(t+1)/2$ y $p_-(t)=(t-1)/2$ cumplen

$$
v(\pm1)=\int_I \left(\tfrac12v(t)+p_\pm(t)v'(t)\right)\,dt.
$$

`extremo_intervalo_de_integral` prueba la fórmula mediante el teorema fundamental del cálculo. `desigualdad_traza_intervalo` controla la suma de los cuadrados de los extremos por ocho veces la energía unidimensional.

En cada cara, el emparejamiento de la fórmula con un elemento $a\in L^2(I)$ se obtiene prolongando $a$ a lo largo de la coordenada normal. Multiplicar esta prolongación por cualquiera de los pesos produce un operador de norma a lo sumo $\sqrt2$, mediante Fubini y la longitud dos del intervalo. Los adjuntos de esos operadores, aplicados a la función y a su derivada débil normal, definen las cuatro componentes de `trazaSobolevCuadrado` directamente sobre clases $L^2$. El par de coordenadas identifica Lebesgue restringida del cuadrado con la medida producto de los intervalos.

El codominio `L2Caras` tiene cuatro componentes indexadas por coordenada y extremo. Cada cara usa Lebesgue unidimensional en el intervalo abierto. `cara_ignora_vertices` expresa que cambiar los valores en los extremos no altera la clase. `trazaSobolevCuadrado_clasica` recupera la evaluación de las funciones clásicas globales $C^1$ mediante Fubini. `trazaSobolevCuadrado_suave` la especializa al tipo de candidatos ya usado en Poisson. `trazaSobolevCuadrado_tendsto` garantiza que toda sucesión que converja en `W12` tiene trazas convergentes a la traza del límite. La definición por adjuntos evita requerir densidad suave para construir el operador. `trazaSobolevCuadrado_norma` da la constante $2\sqrt2$ para la norma máxima de las cuatro caras. `trazaSobolevCuadrado_suma_cuadrados` prueba la cota $32\|v\|_{H^1}^2$ para la suma de las cuatro normas al cuadrado, que corresponde a la constante $4\sqrt2$ en la norma $L^2$ sobre la frontera.

## Núcleo y alcance

`trazaSobolevCuadrado_cero_de_H01` demuestra $H_0^1\subseteq\ker(\operatorname{Tr})$. Las funciones de prueba se anulan en las cuatro caras y la continuidad pasa la identidad a su clausura. Se deduce que una diferencia en $H_0^1$ tiene trazas iguales. `trazas_iguales_de_frontera_puntual` recupera, en particular, la igualdad de trazas para los representantes continuos de igual frontera de la etapa 27.

Queda pendiente la inclusión inversa para todo `W12`, así como identificar la traza con la restricción de un representante solamente continuo. Para la ruta de extensión por cero, la obligación inmediata es demostrar, para cada dirección normal $i$ y toda prueba global $\phi$, que

$$
\int_U (v\,\partial_i\phi + D_iv\,\phi)
=\langle T_{i,+}v,\phi|_{i,+}\rangle
-\langle T_{i,-}v,\phi|_{i,-}\rangle.
$$

La definición de la traza ya proporciona el lado derecho cuando $\phi$ es afín en la coordenada normal. Para el resto, se necesita restar el interpolante afín de los dos valores extremos y aproximar la función resultante con recortes interiores para aplicar la derivada débil. El resto se anula linealmente en las caras normales. Esa anulación debe controlar en $L^2$ el producto con las derivadas de los recortes. Tras extender por cero, aún se necesita verificar la convergencia en $L^2$ del valor y el gradiente bajo contracciones hacia el interior. La aproximación final por molificación con soporte interior ya está disponible en `H1Graph.mem_H01_of_hasCompactSupport` de EllipticPDE. La densidad suave global disponible allí exige `HasC1Boundary`, que no cubre los vértices del cuadrado.

| Parte de C3.23 | Estado |
|---|---|
| (3.80) | Constante óptima y caso de igualdad verificados en la etapa 26. |
| (3.81)–(3.82) | Verificadas para una diferencia en $H_0^1$ y para los representantes continuos de igual frontera de la etapa 27. La deducción a partir de la igualdad de las trazas por caras para dos elementos arbitrarios sigue pendiente. |
| (3.83) | La etapa 27 obtiene la tasa casi segura y ambas convergencias desde P3.15 en sus instancias verificadas, con $\|r\|_2=2\sqrt E$. La extensión a la hipótesis general de traza requiere la inclusión inversa del núcleo. |

Se conserva la prioridad de cerrar la inclusión inversa antes de considerar completa la formulación general. El bloque siguiente del inventario empieza con la arquitectura cuadrática común de L3.24, seguida de Hermite y la construcción de las selecciones de mínimos.

## Verificación

Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. `lake build` ejecuta los controles `#check` y `#print axioms` en el módulo nuevo. Las declaraciones auditadas dependen de `propext`, `Classical.choice` y `Quot.sound`. El SHA-256 del PDF normativo coincide con el inventario.
