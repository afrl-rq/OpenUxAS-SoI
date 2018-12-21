FROM uxas/uxas-build:x86_64 as intermediate

USER root
WORKDIR /UxAS

COPY ./ContainerScriptsAndFiles/getDependencies.sh /UxAS/Installation/
COPY ./tmp/uxas /UxAS/Installation/


RUN cd /UxAS/Installation/ \
 && tr -d '\15\32' < getDependencies.sh > getDependencies01.sh \
 && mv getDependencies01.sh getDependencies.sh \
 && chmod +x getDependencies.sh \ 
 && ./getDependencies.sh uxas /UxAS/Installation/RunTimeFiles

FROM scratch
COPY --from=intermediate /lib64/ld-linux-x86-64.so.2 /lib64/ld-linux-x86-64.so.2 /
COPY --from=intermediate /UxAS/Installation/RunTimeFiles /
ENV LD_LIBRARY_PATH=/usr/local/lib:/lib/x86_64-linux-gnu:/usr/lib/x86_64-linux-gnu:/lib64
ENV PATH=/
ENTRYPOINT ["uxas"]
