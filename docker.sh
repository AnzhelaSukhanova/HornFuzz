CONTAINER_NUM=1

run_container() {
	docker container rm "hornfuzz$1"
	docker run -it \
		-v "$PWD/log$1":/logfile \
		-v "$PWD/hornfuzz-workdir$1":/output \
		--cap-add=SYS_PTRACE --security-opt seccomp=unconfined \
		--name "hornfuzz$1" \
		--network hornfuzz-net \
		hornfuzz
}

if [[ "$@" =~ "--create-net" ]]; then
   docker network create hornfuzz-net
fi
if [[ "$@" =~ "--build-img" ]]; then
   docker build . -t hornfuzz --build-arg arg=$i
fi

for i in `eval echo {1..$CONTAINER_NUM}`; do
	if [[ "$@" =~ "--clean-last" ]]; then
		rm -rf "log$i" "hornfuzz-workdir$i"
		touch "log$i"
	fi
	run_container $i
done

while true
do
	sleep 1h
	for i in `eval echo {1..$CONTAINER_NUM}`; do
		status=`docker inspect -f "{{.State.Status}}" "hornfuzz$i"`
		if [[ $status = "exited" ]]; then
			echo $i
			run_container $i
		fi
	done
done

