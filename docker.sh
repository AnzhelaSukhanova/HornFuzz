CONTAINER_NUM=1

timestamp() {
  date +%Y-%m-%d_%H-%M-%S
}

run_container() {
	docker container rm "hornfuzz$1"
	log_dir="logs$1"
	log="$log_dir/`timestamp`.txt"
	last_log="$log_dir/`ls $log_dir | tail -1`"
	if [[ $last_log == "$log_dir/" ]]; then
		last_log=$log
	fi
	touch "$log"
	docker run -it \
		-v "$PWD/$last_log":/last_logfile \
		-v "$PWD/$log":/logfile \
		-v "$PWD/hornfuzz-workdir$1":/output \
		--cap-add=SYS_PTRACE --security-opt seccomp=unconfined \
		--name "hornfuzz$1" \
		--network hornfuzz-net \
		hornfuzz
	chmod 707 -R "hornfuzz-workdir$1"
}

if [[ "$@" =~ "--create-net" ]]; then
   docker network create hornfuzz-net
fi
if [[ "$@" =~ "--build-img" ]]; then
   docker build . -t hornfuzz --build-arg arg=$i
fi

for i in `eval echo {1..$CONTAINER_NUM}`; do
	if [[ "$@" =~ "--clear-last" ]]; then
		rm -rf "logs$i" "hornfuzz-workdir$i"
		mkdir "logs$i"
	fi
	run_container $i
done


while true
do
	for i in `eval echo {1..24}`; do
		sleep 1h
		for i in `eval echo {1..$CONTAINER_NUM}`; do
			status=`docker inspect -f "{{.State.Status}}" "hornfuzz$i"`
			if [[ $status = "exited" ]]; then
				run_container $i
			fi
		done
	done
	for i in `eval echo {1..$CONTAINER_NUM}`; do
		docker stop "hornfuzz$i"
	done
done

