CONTAINER_NUM=1

timestamp() {
  date +%Y-%m-%d_%H-%M-%S
}

run_container() {
	docker container rm "hornfuzz$1"
	log_dir="logs$1"
	time="`timestamp`.txt"
	touch "$log_dir/$time"
	docker run -it \
		-v "$PWD/$log_dir/$time":/logfile \
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
		rm -rf "logs$i" "hornfuzz-workdir$i"
		mkdir "logs$i"
	fi
	run_container $i
done

while true
do
	sleep 1h
	for i in `eval echo {1..$CONTAINER_NUM}`; do
		status=`docker inspect -f "{{.State.Status}}" "hornfuzz$i"`
		if [[ $status = "exited" ]]; then
			run_container $i
		fi
	done
done

